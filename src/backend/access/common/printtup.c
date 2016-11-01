/*-------------------------------------------------------------------------
 *
 * printtup.c
 *	  Routines to print out tuples to the destination (both frontend
 *	  clients and standalone backends are supported here).
 *
 *
 * Portions Copyright (c) 1996-2016, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * IDENTIFICATION
 *	  src/backend/access/common/printtup.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include "access/printtup.h"
#include "libpq/libpq.h"
#include "libpq/pqformat.h"
#include "tcop/pquery.h"
#include "utils/lsyscache.h"
#include "utils/memdebug.h"
#include "utils/memutils.h"

#include <snappy-c.h>
#define HAVE_PFOR
#ifdef HAVE_PFOR
#include <vint.h>
#include <vp4dc.h>
#include <vp4dd.h>
#endif


static void printtup_startup(DestReceiver *self, int operation,
				 TupleDesc typeinfo);
static bool printtup(TupleTableSlot *slot, DestReceiver *self);
static bool printtup_20(TupleTableSlot *slot, DestReceiver *self);
static bool printtup_internal_20(TupleTableSlot *slot, DestReceiver *self);
static void printtup_shutdown(DestReceiver *self);
static void printtup_destroy(DestReceiver *self);


/* ----------------------------------------------------------------
 *		printtup / debugtup support
 * ----------------------------------------------------------------
 */

/* ----------------
 *		Private state for a printtup destination object
 *
 * NOTE: finfo is the lookup info for either typoutput or typsend, whichever
 * we are using for this column.
 * ----------------
 */
typedef struct
{								/* Per-attribute information */
	Oid			typoutput;		/* Oid for the type's text output fn */
	Oid			typsend;		/* Oid for the type's binary output fn */
	bool		typisvarlena;	/* is it varlena (ie possibly toastable)? */
	int16		format;			/* format code for this column */
	FmgrInfo	finfo;			/* Precomputed call info for output fn */
} PrinttupAttrInfo;

typedef struct
{
	DestReceiver pub;			/* publicly-known function pointers */
	Portal		portal;			/* the Portal we are printing from */
	bool		sendDescrip;	/* send RowDescription at startup? */
	TupleDesc	attrinfo;		/* The attr info we are set up for */
	int			nattrs;
	PrinttupAttrInfo *myinfo;	/* Cached info about each attr */
	MemoryContext tmpcontext;	/* Memory context for per-row workspace */
} DR_printtup;

/* ----------------
 *		Initialize: create a DestReceiver for printtup
 * ----------------
 */
DestReceiver *
printtup_create_DR(CommandDest dest)
{
	DR_printtup *self = (DR_printtup *) palloc0(sizeof(DR_printtup));

	self->pub.receiveSlot = printtup;	/* might get changed later */
	self->pub.rStartup = printtup_startup;
	self->pub.rShutdown = printtup_shutdown;
	self->pub.rDestroy = printtup_destroy;
	self->pub.mydest = dest;

	/*
	 * Send T message automatically if DestRemote, but not if
	 * DestRemoteExecute
	 */
	self->sendDescrip = (dest == DestRemote);

	self->attrinfo = NULL;
	self->nattrs = 0;
	self->myinfo = NULL;
	self->tmpcontext = NULL;

	return (DestReceiver *) self;
}

/*
 * Set parameters for a DestRemote (or DestRemoteExecute) receiver
 */
void
SetRemoteDestReceiverParams(DestReceiver *self, Portal portal)
{
	DR_printtup *myState = (DR_printtup *) self;

	Assert(myState->pub.mydest == DestRemote ||
		   myState->pub.mydest == DestRemoteExecute);

	myState->portal = portal;

	if (PG_PROTOCOL_MAJOR(FrontendProtocol) < 3)
	{
		/*
		 * In protocol 2.0 the Bind message does not exist, so there is no way
		 * for the columns to have different print formats; it's sufficient to
		 * look at the first one.
		 */
		if (portal->formats && portal->formats[0] != 0)
			myState->pub.receiveSlot = printtup_internal_20;
		else
			myState->pub.receiveSlot = printtup_20;
	}
}

static void
printtup_startup(DestReceiver *self, int operation, TupleDesc typeinfo)
{
	DR_printtup *myState = (DR_printtup *) self;
	Portal		portal = myState->portal;

	/*
	 * Create a temporary memory context that we can reset once per row to
	 * recover palloc'd memory.  This avoids any problems with leaks inside
	 * datatype output routines, and should be faster than retail pfree's
	 * anyway.
	 */
	myState->tmpcontext = AllocSetContextCreate(CurrentMemoryContext,
												"printtup",
												ALLOCSET_DEFAULT_SIZES);

	if (PG_PROTOCOL_MAJOR(FrontendProtocol) < 3)
	{
		/*
		 * Send portal name to frontend (obsolete cruft, gone in proto 3.0)
		 *
		 * If portal name not specified, use "blank" portal.
		 */
		const char *portalName = portal->name;

		if (portalName == NULL || portalName[0] == '\0')
			portalName = "blank";

		pq_puttextmessage('P', portalName);
	}

	/*
	 * If we are supposed to emit row descriptions, then send the tuple
	 * descriptor of the tuples.
	 */
	if (myState->sendDescrip)
		SendRowDescriptionMessage(typeinfo,
								  FetchPortalTargetList(portal),
								  portal->formats);

	/* ----------------
	 * We could set up the derived attr info at this time, but we postpone it
	 * until the first call of printtup, for 2 reasons:
	 * 1. We don't waste time (compared to the old way) if there are no
	 *	  tuples at all to output.
	 * 2. Checking in printtup allows us to handle the case that the tuples
	 *	  change type midway through (although this probably can't happen in
	 *	  the current executor).
	 * ----------------
	 */
}

static size_t CHUNK_SIZE = 1000000; // 1 MB chunks

typedef struct  {
	size_t maxsize;
	char *buffer;
	char *copybuffer;
	char *compression_buffer;
	char **bitmask_pointers;
	char **base_pointers;
	char **data_pointers;
	bool *data_is_string;
	bool *data_not_null;
	size_t *attribute_lengths;
	size_t transferred_count;
	size_t tuples_per_chunk;
	size_t total_tuples_send;
	size_t total_tuples;
	size_t count;
} ResultSetBuffer;

static bool initialized = false;
static ResultSetBuffer rsbuf;

static int USE_COMPRESSION = true;
static int MAX_COMPRESSED_LENGTH = 1000000;

//#define ROWWISE_COPY
#define PROTOCOL_NULLMASK

// align number to nearest multiple of eight (e.g. eightalign(15) = 16, eightalign(8) = 8, eightalign(9) = 16)
#define eightalign(sz) ((sz + 7) & ~7)

/*
 * SendRowDescriptionMessage --- send a RowDescription message to the frontend
 *
 * Notes: the TupleDesc has typically been manufactured by ExecTypeFromTL()
 * or some similar function; it does not contain a full set of fields.
 * The targetlist will be NIL when executing a utility function that does
 * not have a plan.  If the targetlist isn't NIL then it is a Query node's
 * targetlist; it is up to us to ignore resjunk columns in it.  The formats[]
 * array pointer might be NULL (if we are doing Describe on a prepared stmt);
 * send zeroes for the format codes in that case.
 */
void
SendRowDescriptionMessage(TupleDesc typeinfo, List *targetlist, int16 *formats)
{
	Form_pg_attribute *attrs = typeinfo->attrs;
	int			natts = typeinfo->natts;
	int			proto = PG_PROTOCOL_MAJOR(FrontendProtocol);
	int			i;
	StringInfoData buf;
	ListCell   *tlist_item = list_head(targetlist);
	char *baseptr;
	size_t rowsize;

	if (!initialized) {
		rsbuf.maxsize = CHUNK_SIZE;
		rsbuf.buffer = malloc(CHUNK_SIZE);
		rsbuf.copybuffer = malloc(CHUNK_SIZE);
		MAX_COMPRESSED_LENGTH = snappy_max_compressed_length(CHUNK_SIZE);
		rsbuf.compression_buffer = malloc(MAX_COMPRESSED_LENGTH);
		initialized = true;
		USE_COMPRESSION = getenv("POSTGRES_COMPRESSION") != NULL;
		if (USE_COMPRESSION) {
			pq_enlargebuffer(MAX_COMPRESSED_LENGTH);
		} else {
			pq_enlargebuffer(CHUNK_SIZE);
		}
	} else {
#ifdef PROTOCOL_NULLMASK
		free(rsbuf.bitmask_pointers);
#endif
		free(rsbuf.base_pointers);
		free(rsbuf.data_pointers);
		free(rsbuf.data_is_string);
		free(rsbuf.attribute_lengths);
		free(rsbuf.data_not_null);
	}
	rsbuf.transferred_count = 0;
	rsbuf.tuples_per_chunk = 0;
	rsbuf.total_tuples_send = 0;
	rsbuf.total_tuples = 0; // FIXME
	rsbuf.count = 0;
#ifdef PROTOCOL_NULLMASK
	rsbuf.bitmask_pointers = malloc(sizeof(char*) * natts);
#endif
	rsbuf.base_pointers = malloc(sizeof(char*) * natts);
	rsbuf.data_pointers = malloc(sizeof(char*) * natts);
	rsbuf.data_is_string = malloc(sizeof(bool) * natts);
	rsbuf.attribute_lengths = malloc(sizeof(size_t) * natts);
	rsbuf.data_not_null = malloc(sizeof(bool) * natts);

	// rowsize in bits
#ifdef PROTOCOL_NULLMASK
	rowsize = natts; // reserve one bit per attribute for the null mask
#else
	rowsize = 0;
#endif

	size_t bytes_left = CHUNK_SIZE - sizeof(int) * natts  - sizeof(size_t) - 1;
	for (i = 0; i < natts; ++i) {
		char category;
		bool preferred;
		ssize_t attribute_length = attrs[i]->attlen;
		get_type_category_preferred(attrs[i]->atttypid, &category, &preferred);
		if ((rsbuf.data_is_string[i] = (category == 'S'))) {
			attribute_length = attrs[i]->atttypmod - 4 + 1; // null terminator
		}
		if (category == 'D') {
			attribute_length = 4; // dates are stored as 4-byte integers
		}
		if (category == 'N' && attribute_length < 0) {
			attribute_length = 4;
		}
		rsbuf.data_not_null[i] = attrs[i]->attnotnull;
		rsbuf.attribute_lengths[i] = attribute_length;
		rowsize += attribute_length * 8; //attribute length is given in bytes; convert to bits
		Assert(attribute_length > 0); // FIXME: deal with Blobs
	}
#ifdef PROTOCOL_NULLMASK
	// only consider chunks of eight rows for easy bitmask alignment
	rsbuf.tuples_per_chunk = eightalign((8 * 8 * (bytes_left)) / (8 * rowsize)) - 8;
#else
	rsbuf.tuples_per_chunk = (8 * 8 * (bytes_left)) / (8 * rowsize);
#endif

#ifdef PROTOCOL_NULLMASK
	// bitmask size per column in bytes
	size_t bitmask_size = eightalign(rsbuf.tuples_per_chunk) / 8;
#endif

	baseptr = rsbuf.buffer + sizeof(size_t) + sizeof(int) + sizeof(char); // new result set message
	for (i = 0; i < natts; ++i) {
#ifdef PROTOCOL_NULLMASK
		rsbuf.bitmask_pointers[i] = baseptr;
		if (!rsbuf.data_not_null[i]) {
			memset(rsbuf.bitmask_pointers[i], 0, bitmask_size); // fill the bitmask with 0 values
			baseptr += bitmask_size;
		}
#endif

		rsbuf.base_pointers[i] = baseptr;
		rsbuf.data_pointers[i] = rsbuf.base_pointers[i] + sizeof(int);

		baseptr += rsbuf.tuples_per_chunk * rsbuf.attribute_lengths[i] + sizeof(int);
	}

	// send a different row descriptor; because it is easier than extending the current one
	// for benchmarking purposes
	pq_beginmessage(&buf, '{'); /* tuple descriptor message type */
	pq_sendint(&buf, USE_COMPRESSION, 4); /* whether or not we are using compression */
	pq_sendint(&buf, CHUNK_SIZE, 4); /* whether or not we are using compression */
	pq_sendint(&buf, natts, 4); /* # of attrs in tuples */
	pq_sendint(&buf, (int) bitmask_size, 4); /* bitmask size per column in bytes */
	for (i = 0; i < natts; ++i) {
		int type = 2;
		pq_sendint(&buf, rsbuf.attribute_lengths[i], 4); // attribute length of this tuple
		if (rsbuf.data_is_string[i]) {
			type = 1;
		}
		// FIXME: floating point values not handled correctly here (they should be type = 3)
		pq_sendint(&buf, type, 4); // type of the tuple (for printing purposes only)		
		// whether or not there are NULL values in this column
		pq_sendint(&buf, rsbuf.data_not_null[i], 4);
	}
	pq_endmessage(&buf);


	Assert(rsbuf.tuples_per_chunk > 0);

	pq_beginmessage(&buf, 'T'); /* tuple descriptor message type */
	pq_sendint(&buf, natts, 2); /* # of attrs in tuples */

	for (i = 0; i < natts; ++i)
	{
		Oid			atttypid = attrs[i]->atttypid;
		int32		atttypmod = attrs[i]->atttypmod;

		pq_sendstring(&buf, NameStr(attrs[i]->attname));
		/* column ID info appears in protocol 3.0 and up */
		if (proto >= 3)
		{
			/* Do we have a non-resjunk tlist item? */
			while (tlist_item &&
				   ((TargetEntry *) lfirst(tlist_item))->resjunk)
				tlist_item = lnext(tlist_item);
			if (tlist_item)
			{
				TargetEntry *tle = (TargetEntry *) lfirst(tlist_item);

				pq_sendint(&buf, tle->resorigtbl, 4);
				pq_sendint(&buf, tle->resorigcol, 2);
				tlist_item = lnext(tlist_item);
			}
			else
			{
				/* No info available, so send zeroes */
				pq_sendint(&buf, 0, 4);
				pq_sendint(&buf, 0, 2);
			}
		}
		/* If column is a domain, send the base type and typmod instead */
		atttypid = getBaseTypeAndTypmod(atttypid, &atttypmod);
		pq_sendint(&buf, (int) atttypid, sizeof(atttypid));
		pq_sendint(&buf, attrs[i]->attlen, sizeof(attrs[i]->attlen));
		/* typmod appears in protocol 2.0 and up */
		if (proto >= 2)
			pq_sendint(&buf, atttypmod, sizeof(atttypmod));
		/* format info appears in protocol 3.0 and up */
		if (proto >= 3)
		{
			if (formats)
				pq_sendint(&buf, formats[i], 2);
			else
				pq_sendint(&buf, 0, 2);
		}
	}
	pq_endmessage(&buf);
}

/*
 * Get the lookup info that printtup() needs
 */
static void
printtup_prepare_info(DR_printtup *myState, TupleDesc typeinfo, int numAttrs)
{
	int16	   *formats = myState->portal->formats;
	int			i;

	/* get rid of any old data */
	if (myState->myinfo)
		pfree(myState->myinfo);
	myState->myinfo = NULL;

	myState->attrinfo = typeinfo;
	myState->nattrs = numAttrs;
	if (numAttrs <= 0)
		return;

	myState->myinfo = (PrinttupAttrInfo *)
		palloc0(numAttrs * sizeof(PrinttupAttrInfo));

	for (i = 0; i < numAttrs; i++)
	{
		PrinttupAttrInfo *thisState = myState->myinfo + i;
		int16		format = (formats ? formats[i] : 0);

		thisState->format = format;
		if (format == 0)
		{
			getTypeOutputInfo(typeinfo->attrs[i]->atttypid,
							  &thisState->typoutput,
							  &thisState->typisvarlena);
			fmgr_info(thisState->typoutput, &thisState->finfo);
		}
		else if (format == 1)
		{
			getTypeBinaryOutputInfo(typeinfo->attrs[i]->atttypid,
									&thisState->typsend,
									&thisState->typisvarlena);
			fmgr_info(thisState->typsend, &thisState->finfo);
		}
		else
			ereport(ERROR,
					(errcode(ERRCODE_INVALID_PARAMETER_VALUE),
					 errmsg("unsupported format code: %d", format)));
	}
}


static size_t transmitted_size = 0;

/* ----------------
 *		printtup --- print a tuple in protocol 3.0
 * ----------------
 */
static bool
printtup(TupleTableSlot *slot, DestReceiver *self)
{
	TupleDesc	typeinfo = slot->tts_tupleDescriptor;
	DR_printtup *myState = (DR_printtup *) self;
	MemoryContext oldcontext;
	StringInfoData buf;
	int			natts = typeinfo->natts;
	int			i;

	/* Make sure the tuple is fully deconstructed */
	slot_getallattrs(slot);

	rsbuf.count++;
	// set bit in null mask
	size_t byte = rsbuf.count / 8;
	int bit = rsbuf.count % 8;
	int or_bit = 1 << bit;
	// copy the data of this row into the buffer
	for (i = 0; i < natts; ++i) {
		Datum attr = slot->tts_values[i];
		if (!rsbuf.data_not_null[i] && slot->tts_isnull[i]) {
#ifdef PROTOCOL_NULLMASK
			rsbuf.bitmask_pointers[i][byte] |= or_bit;
#else
			if (rsbuf.data_is_string[i]) {
				// NULL value is an illegal UTF-8 bit
				rsbuf.data_pointers[i][0] = '\200';
				rsbuf.data_pointers[i][1] = '\0';
				rsbuf.data_pointers[i] += 2;				
			} else {
				memset(rsbuf.data_pointers[i], 1, rsbuf.attribute_lengths[i]);
				rsbuf.data_pointers[i] += rsbuf.attribute_lengths[i];
			}
#endif
		} else {
			if (rsbuf.data_is_string[i]) {
				int len = VARSIZE_ANY_EXHDR(attr);
				memcpy(rsbuf.data_pointers[i], ((char*)attr) + 1, len);
				rsbuf.data_pointers[i][len] = '\0';
				rsbuf.data_pointers[i] += len + 1;
			} else {
				memcpy(rsbuf.data_pointers[i], &attr, rsbuf.attribute_lengths[i]);
				rsbuf.data_pointers[i] += rsbuf.attribute_lengths[i];
			}
		}
	}
	// check if the buffer is full; if it is, we send it
	if (rsbuf.count >= rsbuf.tuples_per_chunk || 
		rsbuf.total_tuples_send + rsbuf.count == 1000000 || /* always transfer on 1M or 10M total tuples: hacky workaround for not knowing when we reach the end */
		rsbuf.total_tuples_send + rsbuf.count == 10000000) {
		int nullmask_size = 0;
		*((int*) (rsbuf.buffer + 5)) = (int) rsbuf.count; // amount of rows to send
#ifdef PROTOCOL_NULLMASK
		nullmask_size = (int) (rsbuf.base_pointers[0] - rsbuf.bitmask_pointers[0]); // amount of rows normally encoded in a chunk
#endif

		size_t chunk_data = sizeof(int) * 2;
		for (i = 0; i < natts; ++i) {
			if (i > 0) {
				if (!(rsbuf.data_pointers[i - 1] <= rsbuf.bitmask_pointers[i])) {
					printf("Out of buffer exception (%zu)\n", rsbuf.data_pointers[i - 1] - rsbuf.bitmask_pointers[i]);
				}
			}
#ifdef PROTOCOL_NULLMASK
			chunk_data += rsbuf.data_pointers[i] - rsbuf.bitmask_pointers[i];
#else
			chunk_data += rsbuf.data_pointers[i] - rsbuf.base_pointers[i];
#endif
			(*(int*) (rsbuf.base_pointers[i])) = (int) (rsbuf.data_pointers[i] - rsbuf.base_pointers[i]);
		}
		if (USE_COMPRESSION) {
			// use snappy to compress the data first
			char *buffer = rsbuf.copybuffer;
			memcpy(buffer, &rsbuf.count, 4);
			buffer += 4;
			memcpy(buffer,&nullmask_size, 4);
			buffer += 4;
			for (i = 0; i < natts; ++i) {
#ifdef PROTOCOL_NULLMASK		
#ifdef HAVE_PFOR
				if (rsbuf.attribute_lengths[i] == sizeof(int)) {
				       int *length_pointer;
				       int n = rsbuf.count;
				       char *datain;
				       char *bufstart;
				       // first copy the bitmask into the buffer
				       memcpy(buffer, rsbuf.bitmask_pointers[i], rsbuf.base_pointers[i] - rsbuf.bitmask_pointers[i]);
				       buffer += rsbuf.base_pointers[i] - rsbuf.bitmask_pointers[i];
				       // now compress the actual column data into the buffer using PFOR
				       length_pointer = (int*) buffer;
				       bufstart = buffer;
				       buffer += sizeof(int);
				       datain = rsbuf.base_pointers[i] + sizeof(int);
				       while(n > 0) {
				               int elements = n > 128 ? 128 : n;
				               if (elements < 128) {
				                       memcpy(buffer, datain, elements * sizeof(int));
				                       buffer += elements * sizeof(int);
				               } else {
				                       buffer = p4dencv32(datain, elements, buffer);
				                       if (!buffer) {
				                               printf("PFOR compression failed.\n");
				                               return -1;
				                       }
				               }
				               datain += elements * sizeof(int);
				               n -= elements;
				       }
				       *length_pointer = buffer - bufstart;
				       //printf("PFOR Compression successful (%d -> %d)\n", (int)(rsbuf.count * sizeof(int)), (int)(buffer - bufstart));
				} else 
#endif
				{
				       // copy all the data of this column into the buffer
				       memcpy(buffer, rsbuf.bitmask_pointers[i], rsbuf.data_pointers[i] - rsbuf.bitmask_pointers[i]);
				       buffer += rsbuf.data_pointers[i] - rsbuf.bitmask_pointers[i];
				}
#else
				memcpy(buffer, rsbuf.base_pointers[i], rsbuf.data_pointers[i] - rsbuf.base_pointers[i]);
				buffer += rsbuf.data_pointers[i] - rsbuf.base_pointers[i];
#endif		
			}
			size_t compressed_length = MAX_COMPRESSED_LENGTH;
			if (snappy_compress(rsbuf.copybuffer, buffer - rsbuf.copybuffer, rsbuf.compression_buffer, &compressed_length) != SNAPPY_OK) {
				printf("Failed to compress data.\n");
			} else {
				//printf("Succeeded in compressing {%zu -> %zu}.\n", buffer - rsbuf.copybuffer, compressed_length);
			}
			uint32		n32;
			n32 = htonl((uint32) (compressed_length + 4));
			pq_flush();
			pq_putbytes("*", 1);
			pq_putbytes((char *) &n32, 4);
			pq_putbytes(rsbuf.compression_buffer, compressed_length);
			pq_flush();
		} else {
			// no compression, directly write bytes to the underlying buffer
			uint32		n32;
			n32 = htonl((uint32) (chunk_data + 4));
			pq_flush();
			pq_putbytes("*", 1);
			pq_putbytes((char *) &n32, 4);
			pq_putbytes(&rsbuf.count, 4);
			pq_putbytes(&nullmask_size, 4);
			for (i = 0; i < natts; ++i) {
#ifdef PROTOCOL_NULLMASK
				pq_putbytes(rsbuf.bitmask_pointers[i], rsbuf.data_pointers[i] - rsbuf.bitmask_pointers[i]);
#else
				pq_putbytes(rsbuf.base_pointers[i], rsbuf.data_pointers[i] - rsbuf.base_pointers[i]);
#endif		
			}
			pq_flush();
		}
/*

		}
		for(int i = 1; i < natts; i++) {
			printf("%p (%zu); total: %zu\n", rsbuf.data_pointers[i], rsbuf.data_pointers[i] - rsbuf.base_pointers[i - 1], rsbuf.base_pointers[i] - rsbuf.base_pointers[0]);
		}
		printf("Packet %zu-%zu.\nRows: %zu, Length: %zu\n", rsbuf.total_tuples_send, rsbuf.total_tuples_send + rsbuf.count, rsbuf.count, chunk_data);*/
		for (i = 0; i < natts; ++i) {
			// reset the base pointer for the next time something is send
			rsbuf.data_pointers[i] = rsbuf.base_pointers[i] + sizeof(int);
		}

		// // actually send the message to the client
		// //pq_putmessage_noblock('*', rsbuf.buffer + 5, chunk_data);
		// if (pq_writemessage('*', chunk_data, rsbuf.buffer, rsbuf.data_pointers[natts - 1]) != 0) {
		// 	return false;
		// }
		rsbuf.total_tuples_send += rsbuf.count;
		rsbuf.count = 0;
		transmitted_size += chunk_data;
	}

	return true;

	/* Set or update my derived attribute info, if needed */
	if (myState->attrinfo != typeinfo || myState->nattrs != natts)
		printtup_prepare_info(myState, typeinfo, natts);

	/* Make sure the tuple is fully deconstructed */
	slot_getallattrs(slot);

	/* Switch into per-row context so we can recover memory below */
	oldcontext = MemoryContextSwitchTo(myState->tmpcontext);

	/*
	 * Prepare a DataRow message (note buffer is in per-row context)
	 */
	pq_beginmessage(&buf, 'D');

	pq_sendint(&buf, natts, 2);

	/*
	 * send the attributes of this tuple
	 */
	for (i = 0; i < natts; ++i)
	{
		PrinttupAttrInfo *thisState = myState->myinfo + i;
		Datum		attr = slot->tts_values[i];

		if (slot->tts_isnull[i])
		{
			pq_sendint(&buf, -1, 4);
			continue;
		}

		/*
		 * Here we catch undefined bytes in datums that are returned to the
		 * client without hitting disk; see comments at the related check in
		 * PageAddItem().  This test is most useful for uncompressed,
		 * non-external datums, but we're quite likely to see such here when
		 * testing new C functions.
		 */
		if (thisState->typisvarlena)
			VALGRIND_CHECK_MEM_IS_DEFINED(DatumGetPointer(attr),
										  VARSIZE_ANY(attr));

		if (thisState->format == 0)
		{
			/* Text output */
			char	   *outputstr;

			outputstr = OutputFunctionCall(&thisState->finfo, attr);
			pq_sendcountedtext(&buf, outputstr, strlen(outputstr), false);
		}
		else
		{
			/* Binary output */
			bytea	   *outputbytes;

			outputbytes = SendFunctionCall(&thisState->finfo, attr);
			pq_sendint(&buf, VARSIZE(outputbytes) - VARHDRSZ, 4);
			pq_sendbytes(&buf, VARDATA(outputbytes),
						 VARSIZE(outputbytes) - VARHDRSZ);
		}
	}

	pq_endmessage(&buf);

	/* Return to caller's context, and flush row's temporary memory */
	MemoryContextSwitchTo(oldcontext);
	MemoryContextReset(myState->tmpcontext);

	return true;
}

/* ----------------
 *		printtup_20 --- print a tuple in protocol 2.0
 * ----------------
 */
static bool
printtup_20(TupleTableSlot *slot, DestReceiver *self)
{
	TupleDesc	typeinfo = slot->tts_tupleDescriptor;
	DR_printtup *myState = (DR_printtup *) self;
	MemoryContext oldcontext;
	StringInfoData buf;
	int			natts = typeinfo->natts;
	int			i,
				j,
				k;

	/* Set or update my derived attribute info, if needed */
	if (myState->attrinfo != typeinfo || myState->nattrs != natts)
		printtup_prepare_info(myState, typeinfo, natts);

	/* Make sure the tuple is fully deconstructed */
	slot_getallattrs(slot);

	/* Switch into per-row context so we can recover memory below */
	oldcontext = MemoryContextSwitchTo(myState->tmpcontext);

	/*
	 * tell the frontend to expect new tuple data (in ASCII style)
	 */
	pq_beginmessage(&buf, 'D');

	/*
	 * send a bitmap of which attributes are not null
	 */
	j = 0;
	k = 1 << 7;
	for (i = 0; i < natts; ++i)
	{
		if (!slot->tts_isnull[i])
			j |= k;				/* set bit if not null */
		k >>= 1;
		if (k == 0)				/* end of byte? */
		{
			pq_sendint(&buf, j, 1);
			j = 0;
			k = 1 << 7;
		}
	}
	if (k != (1 << 7))			/* flush last partial byte */
		pq_sendint(&buf, j, 1);

	/*
	 * send the attributes of this tuple
	 */
	for (i = 0; i < natts; ++i)
	{
		PrinttupAttrInfo *thisState = myState->myinfo + i;
		Datum		attr = slot->tts_values[i];
		char	   *outputstr;

		if (slot->tts_isnull[i])
			continue;

		Assert(thisState->format == 0);

		outputstr = OutputFunctionCall(&thisState->finfo, attr);
		pq_sendcountedtext(&buf, outputstr, strlen(outputstr), true);
	}

	pq_endmessage(&buf);

	/* Return to caller's context, and flush row's temporary memory */
	MemoryContextSwitchTo(oldcontext);
	MemoryContextReset(myState->tmpcontext);

	return true;
}

/* ----------------
 *		printtup_shutdown
 * ----------------
 */
static void
printtup_shutdown(DestReceiver *self)
{
	DR_printtup *myState = (DR_printtup *) self;

	if (myState->myinfo)
		pfree(myState->myinfo);
	myState->myinfo = NULL;

	myState->attrinfo = NULL;

	if (myState->tmpcontext)
		MemoryContextDelete(myState->tmpcontext);
	myState->tmpcontext = NULL;
}

/* ----------------
 *		printtup_destroy
 * ----------------
 */
static void
printtup_destroy(DestReceiver *self)
{
	pfree(self);
}

/* ----------------
 *		printatt
 * ----------------
 */
static void
printatt(unsigned attributeId,
		 Form_pg_attribute attributeP,
		 char *value)
{
	printf("\t%2d: %s%s%s%s\t(typeid = %u, len = %d, typmod = %d, byval = %c)\n",
		   attributeId,
		   NameStr(attributeP->attname),
		   value != NULL ? " = \"" : "",
		   value != NULL ? value : "",
		   value != NULL ? "\"" : "",
		   (unsigned int) (attributeP->atttypid),
		   attributeP->attlen,
		   attributeP->atttypmod,
		   attributeP->attbyval ? 't' : 'f');
}

/* ----------------
 *		debugStartup - prepare to print tuples for an interactive backend
 * ----------------
 */
void
debugStartup(DestReceiver *self, int operation, TupleDesc typeinfo)
{
	int			natts = typeinfo->natts;
	Form_pg_attribute *attinfo = typeinfo->attrs;
	int			i;

	/*
	 * show the return type of the tuples
	 */
	for (i = 0; i < natts; ++i)
		printatt((unsigned) i + 1, attinfo[i], NULL);
	printf("\t----\n");
}

/* ----------------
 *		debugtup - print one tuple for an interactive backend
 * ----------------
 */
bool
debugtup(TupleTableSlot *slot, DestReceiver *self)
{
	TupleDesc	typeinfo = slot->tts_tupleDescriptor;
	int			natts = typeinfo->natts;
	int			i;
	Datum		attr;
	char	   *value;
	bool		isnull;
	Oid			typoutput;
	bool		typisvarlena;

	for (i = 0; i < natts; ++i)
	{
		attr = slot_getattr(slot, i + 1, &isnull);
		if (isnull)
			continue;
		getTypeOutputInfo(typeinfo->attrs[i]->atttypid,
						  &typoutput, &typisvarlena);

		value = OidOutputFunctionCall(typoutput, attr);

		printatt((unsigned) i + 1, typeinfo->attrs[i], value);
	}
	printf("\t----\n");

	return true;
}

/* ----------------
 *		printtup_internal_20 --- print a binary tuple in protocol 2.0
 *
 * We use a different message type, i.e. 'B' instead of 'D' to
 * indicate a tuple in internal (binary) form.
 *
 * This is largely same as printtup_20, except we use binary formatting.
 * ----------------
 */
static bool
printtup_internal_20(TupleTableSlot *slot, DestReceiver *self)
{
	TupleDesc	typeinfo = slot->tts_tupleDescriptor;
	DR_printtup *myState = (DR_printtup *) self;
	MemoryContext oldcontext;
	StringInfoData buf;
	int			natts = typeinfo->natts;
	int			i,
				j,
				k;

	/* Set or update my derived attribute info, if needed */
	if (myState->attrinfo != typeinfo || myState->nattrs != natts)
		printtup_prepare_info(myState, typeinfo, natts);

	/* Make sure the tuple is fully deconstructed */
	slot_getallattrs(slot);

	/* Switch into per-row context so we can recover memory below */
	oldcontext = MemoryContextSwitchTo(myState->tmpcontext);

	/*
	 * tell the frontend to expect new tuple data (in binary style)
	 */
	pq_beginmessage(&buf, 'B');

	/*
	 * send a bitmap of which attributes are not null
	 */
	j = 0;
	k = 1 << 7;
	for (i = 0; i < natts; ++i)
	{
		if (!slot->tts_isnull[i])
			j |= k;				/* set bit if not null */
		k >>= 1;
		if (k == 0)				/* end of byte? */
		{
			pq_sendint(&buf, j, 1);
			j = 0;
			k = 1 << 7;
		}
	}
	if (k != (1 << 7))			/* flush last partial byte */
		pq_sendint(&buf, j, 1);

	/*
	 * send the attributes of this tuple
	 */
	for (i = 0; i < natts; ++i)
	{
		PrinttupAttrInfo *thisState = myState->myinfo + i;
		Datum		attr = slot->tts_values[i];
		bytea	   *outputbytes;

		if (slot->tts_isnull[i])
			continue;

		Assert(thisState->format == 1);

		outputbytes = SendFunctionCall(&thisState->finfo, attr);
		pq_sendint(&buf, VARSIZE(outputbytes) - VARHDRSZ, 4);
		pq_sendbytes(&buf, VARDATA(outputbytes),
					 VARSIZE(outputbytes) - VARHDRSZ);
	}

	pq_endmessage(&buf);

	/* Return to caller's context, and flush row's temporary memory */
	MemoryContextSwitchTo(oldcontext);
	MemoryContextReset(myState->tmpcontext);

	return true;
}
