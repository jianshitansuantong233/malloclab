/*
 * mm.c -  Simple allocator based on segregated free lists,
 *         first fit placement, and boundary tag coalescing.
 *
 * Each block has header and footer of the form:
 *
 *      31                     3  2  1  0
 *      -----------------------------------
 *     | s  s  s  s  ... s  s  s  0  0  a/f
 *      -----------------------------------
 *
 * where s are the meaningful size bits and a/f is set
 * iff the block is allocated. The list has the following form:
 *
 * begin                                                          end
 * heap                                                           heap
 *  -----------------------------------------------------------------
 * |  pad   | hdr(8:a) | ftr(8:a) | zero or more usr blks | hdr(8:a) |
 *  -----------------------------------------------------------------
 *          |       prologue      |                       | epilogue |
 *          |         block       |                       | block    |
 *
 * The allocated prologue and epilogue blocks are overhead that
 * eliminate edge conditions during coalescing.
 *
 *I put the array for segregated lists before prologue block.
 *Each free block has a number of differences in addresses between
 *its previous block in the list and its successor in the list.
 */

#include <stdio.h>
#include <unistd.h>
#include <string.h>
#include <stdlib.h>
#include "mm.h"
#include "memlib.h"
#include <stdint.h>

/* Your info */
team_t team = { 
    /* First and last name */
    "Feiqian Zhu",
    /* UID */
    "905108312",
    "hardest one ever"
}; 

/* $begin mallocmacros */
/* Basic constants and macros */
#define WSIZE       4       /* word size (bytes) */  
#define DSIZE       8       /* doubleword size (bytes) */
#define CHUNKSIZE  (1<<16)  /* initial heap size (bytes) */
#define OVERHEAD    8       /* overhead of header and footer (bytes) */

#define MAX(x, y) ((x) > (y)? (x) : (y))  
#define MIN(x, y) ((x) > (y)? (y) : (x))
/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)       (*(uint32_t *)(p))
#define PUT(p, val)  (*(uint32_t *)(p) = (val))  

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)  
#define FTRP(bp)       ((char *)(bp) + (GET_SIZE(HDRP(bp)) - DSIZE))

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* GET_I and PUT_I are used for grabbing differences in addresses*/
#define GET_I(p) (*(int32_t *)(p))
#define PUT_I(p,val) (*(int32_t *)(p) = (val))
/* SUCC and PRED are used to calculate the address of previous block
and successor in the free list*/
#define SUCC(bp) ((char*)bp + GET_I((char*)(bp) + WSIZE))
#define PRED(bp) ((char *)(bp) + GET_I((char*)bp))

/* $end mallocmacros */

/* Global variables */
static char *heap_listp;  /* pointer to first block */  
static char **ptr_classes;/* pointer to the array of lists*/
/* function prototypes for internal helper routines */
inline static void *extend_heap(size_t words);
inline static void place(void *bp, size_t asize);
inline static void *find_fit(size_t asize);
inline static void *coalesce(void *bp);
static void printblock(void *bp); 
static void checkblock(void *bp);
/* pointer to the array of lists*/
inline static void delete_from_class(char *bp, int prev);
inline static void append_to_class(char *bp, int size);
/* 
 * mm_init - Initialize the memory manager 
 */
/* $begin mminit */
int mm_init(void) 
{
	/*initialize the array of free lists*/
	if ((ptr_classes = (char **)mem_sbrk(7 * DSIZE)) == NULL) {
		return -1;
	}
	else {
		ptr_classes[0] = NULL;
		ptr_classes[1] = NULL;
		ptr_classes[2] = NULL;
		ptr_classes[3] = NULL;
		ptr_classes[4] = NULL;
		ptr_classes[5] = NULL;
	}
	/* create the initial empty heap */
    if ((heap_listp = (char *)mem_sbrk(4*WSIZE)) == NULL)
	return -1;
    PUT(heap_listp, 0);                        /* alignment padding */
    PUT(heap_listp+WSIZE, PACK(OVERHEAD, 1));  /* prologue header */ 
    PUT(heap_listp+DSIZE, PACK(OVERHEAD, 1));  /* prologue footer */ 
    PUT(heap_listp+WSIZE+DSIZE, PACK(0, 1));   /* epilogue header */
    heap_listp += DSIZE;
	
    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
	if (extend_heap(CHUNKSIZE / WSIZE) == NULL) {
		return -1;
	}
	/*Also part of initialization*/
	ptr_classes[6] = heap_listp + 8;
	PUT(ptr_classes[6], 0);
	PUT(ptr_classes[6] + 4, 0);
    return 0;
}
/* $end mminit */

/* 
 * mm_malloc - Allocate a block with at least size bytes of payload 
 */
/* $begin mmmalloc */
void *mm_malloc(size_t size) 
{
    uint32_t asize;      /* adjusted block size */
    uint32_t extendsize; /* amount to extend heap if no fit */
    char *bp;      

    /* Ignore spurious requests */
    if (size <= 0)
	return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)
	asize = DSIZE + OVERHEAD;
    else
	asize = DSIZE * ((size + (OVERHEAD) + (DSIZE-1)) / DSIZE);
    
    /* Search the free list for a fit */
    if ((bp = (char *)find_fit(asize)) != NULL) {
		place(bp, asize);
		return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MIN(asize,CHUNKSIZE);
	if ((bp = (char *)extend_heap(extendsize / WSIZE)) == NULL) {
		return NULL;
	}
    place(bp, asize);
    return bp;
} 
/* $end mmmalloc */

/* 
 * mm_free - Free a block 
 */
/* $begin mmfree */
void mm_free(void *bp)
{
    uint32_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

/* $end mmfree */

/*
 * mm_realloc - naive implementation of mm_realloc
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *newp;
    size_t copySize;

    if ((newp = mm_malloc(size)) == NULL) {
	printf("ERROR: mm_malloc failed in mm_realloc\n");
	exit(1);
    }
    copySize = GET_SIZE(HDRP(ptr));
    if (size < copySize)
      copySize = size;
    memcpy(newp, ptr, copySize);
    mm_free(ptr);
    return newp;
}

/* 
 * mm_checkheap - Check the heap for consistency 
 */
void mm_checkheap(int verbose) 
{
    char *bp = heap_listp;

    if (verbose)
	printf("Heap (%p):\n", heap_listp);

    if ((GET_SIZE(HDRP(heap_listp)) != DSIZE) || !GET_ALLOC(HDRP(heap_listp)))
	printf("Bad prologue header\n");
    checkblock(heap_listp);

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
	if (verbose) 
	    printblock(bp);
	checkblock(bp);
    }
     
    if (verbose)
	printblock(bp);
    if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp))))
	printf("Bad epilogue header\n");
}

/* The remaining routines are internal helper routines */

/* 
 * extend_heap - Extend heap with free block and return its block pointer
 */
/* $begin mmextendheap */
inline static void *extend_heap(size_t words) 
{
    char *bp;
    uint32_t size;
	
    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((bp = (char *)mem_sbrk(size)) == (void *)-1) 
	return NULL;
    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));         /* free block header */
    PUT(FTRP(bp), PACK(size, 0));         /* free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* new epilogue header */
	
	/* Coalesce if the previous block was free */
    return coalesce(bp);
}
/* $end mmextendheap */

/* 
 * place - Place block of asize bytes at start of free block bp 
 *         and split if remainder would be at least minimum block size
 */
/* $begin mmplace */
/* $begin mmplace-proto */
inline static void place(void *bp, size_t asize)
/* $end mmplace-proto */
{
    uint32_t csize = GET_SIZE(HDRP(bp));   
	delete_from_class(bp, 2);
    if ((csize - asize) >= (DSIZE + OVERHEAD)) { 
		PUT(HDRP(bp), PACK(asize, 1));
		PUT(FTRP(bp), PACK(asize, 1));
		bp = NEXT_BLKP(bp);
		PUT(HDRP(bp), PACK(csize-asize, 0));
		PUT(FTRP(bp), PACK(csize-asize, 0));
		append_to_class(bp, csize - asize);
    }
    else { 
		PUT(HDRP(bp), PACK(csize, 1));
		PUT(FTRP(bp), PACK(csize, 1));
    }

}
/* $end mmplace */

/*
 * find_fit - Find a fit for a block with asize bytes
 * According to the size we want to malloc,
 * go to its corresponding class first.
 * If the first element in the list does not fit,
 * go to next non-NULL element.
 */

inline static void *find_fit(size_t asize)
{ 
    /* first fit search */
    char *bp;
	char **temp = NULL;
	int increment = 0;
	if (asize <= 512) {
		for (; ; increment += 1) {
			if (ptr_classes[0 + increment] != NULL) {
				if ((int)(GET_SIZE(HDRP(ptr_classes[0 + increment])) - asize) >= 0) {
					temp = &ptr_classes[0 + increment];
					break;
				}
			}
			if (increment == 6) {
				return NULL;
			}
		}
		return *temp;
	}
	else if (asize <= 1024) {
		for (; ; increment += 1) {
			if (ptr_classes[1 + increment] != NULL ) {
				if ((int)(GET_SIZE(HDRP(ptr_classes[1 + increment])) - asize) >= 0) {
					temp = &ptr_classes[1 + increment];
					break;
				}
			}
			if (increment == 5) {
				return NULL;
			}
		}
		return *temp;
	}
	else if (asize <= 2048) {
		for (; ; increment += 1) {
			if (ptr_classes[2 + increment] != NULL) {
				if ((int)(GET_SIZE(HDRP(ptr_classes[2 + increment])) - asize) >= 0) {
					temp = &ptr_classes[2 + increment];
					break;
				}
			}
			if (increment == 4) {
				return NULL;
			}
		}
		return *temp;
	}
	else if (asize <= 4096) {
		for (; ; increment += 1) {
			if (ptr_classes[3 + increment] != NULL) {
				if ((int)(GET_SIZE(HDRP(ptr_classes[3 + increment])) - asize) >= 0) {
					temp = &ptr_classes[3 + increment];
					break;
				}
			}
			if (increment == 3) {
				return NULL;
			}
		}
		return *temp;
	}
	else if (asize <= 8192) {
		for (; ; increment += 1) {
			if (ptr_classes[4 + increment] != NULL) {
				if ((int)(GET_SIZE(HDRP(ptr_classes[4 + increment])) - asize) >= 0) {
					temp = &ptr_classes[4 + increment];
					break;
				}
			}
			if (increment == 2) {
				return NULL;
			}
		}
		return *temp;
	}
	else if (asize <= 16384) {
		for (; ; increment += 1) {
			if (ptr_classes[5 + increment] != NULL) {
				if ((int)(GET_SIZE(HDRP(ptr_classes[5 + increment])) - asize) >= 0) {
					temp = &ptr_classes[5 + increment];
					break;
				}
			}
			if (increment == 1) {
				return NULL;
			}
		}
		return *temp;
	}
	else {
		if (ptr_classes[6] != NULL) {
			if ((int)(GET_SIZE(HDRP(ptr_classes[6])) - asize) >= 0) {
				return ptr_classes[6];
			}
			else {
				return NULL;
			}
		}
		else {
			return NULL;
		}
	}
	
	/*for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
	if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
	    return bp;
	}
    }
    return NULL; /* no fit */
}

/*
 * coalesce - boundary tag coalescing. Return ptr to coalesced block
 */
inline static void *coalesce(void *bp) 
{
    uint32_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    uint32_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    uint32_t size = GET_SIZE(HDRP(bp));
    if (prev_alloc && next_alloc) {            /* Case 1 */
		append_to_class(bp, size);
    }

    else if (prev_alloc && !next_alloc) {      /* Case 2 */
		int next_size = GET_SIZE(HDRP(NEXT_BLKP(bp)));
		size += next_size;
		delete_from_class(bp, 0);
		PUT(HDRP(bp), PACK(size, 0));
		PUT(FTRP(bp), PACK(size,0));
		append_to_class(bp, size);
	}

    else if (!prev_alloc && next_alloc) {      /* Case 3 */
		int prev_size = GET_SIZE(HDRP(PREV_BLKP(bp)));
		size += prev_size;
		delete_from_class(bp, 1);
		PUT(FTRP(bp), PACK(size, 0));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);
		append_to_class(bp, size);
    }

	else {                                     /* Case 4 */
		size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
			GET_SIZE(FTRP(NEXT_BLKP(bp)));
		delete_from_class(bp, 1);
		delete_from_class(bp, 0);
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);
		append_to_class(bp, size);
	}
    return bp;
}


static void printblock(void *bp) 
{
    uint32_t hsize, halloc, fsize, falloc;

    hsize = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp));  
    fsize = GET_SIZE(FTRP(bp));
    falloc = GET_ALLOC(FTRP(bp));  
    
    if (hsize == 0) {
	printf("%p: EOL\n", bp);
	return;
    }

    printf("%p: header: [%d:%c] footer: [%d:%c]\n", bp, 
	   hsize, (halloc ? 'a' : 'f'), 
	   fsize, (falloc ? 'a' : 'f')); 
}

static void checkblock(void *bp) 
{
    if ((uint32_t)bp % 8)
	printf("Error: %p is not doubleword aligned\n", bp);
    if (GET(HDRP(bp)) != GET(FTRP(bp)))
	printf("Error: header does not match footer\n");
}
/*Delete a free block from its list.
 *prev is used to indicate whether the previous block
 *or the next block is going to be deleted. Mainly
 *used for coalesce.
 *The idea is like find_fit and append_to_class:
 *according to the size of the block we want to free,
 *go to its corresponding list.
 *Depending on whether it is a head or foot or somewhere between,
 *change corresponding prev and succ.
 */

inline static void delete_from_class(char* bp, int prev) {
	char* ptr = NULL;
	int ptr_size = 0;
	switch(prev)
	{
	case 0:
		ptr_size = GET_SIZE(HDRP(NEXT_BLKP(bp)));
		ptr = NEXT_BLKP(bp);
		break;
	case 1:
		ptr_size = GET_SIZE(HDRP(PREV_BLKP(bp)));
		ptr = PREV_BLKP(bp);
		break;
	case 2:
		ptr = bp;
		ptr_size = GET_SIZE(HDRP(bp));
		break;
	}
	if (ptr_size <= 512) {
		if (ptr == ptr_classes[0]) {
			ptr_classes[0] = GET(ptr + 4) == 0 ? NULL : SUCC(ptr);
		}
		else {
			if (GET(ptr + 4) == 0) {
				PUT(PRED(ptr) + 4, 0);
			}
			else {
				PUT(PRED(ptr) + 4, SUCC(ptr) - PRED(ptr));
				PUT(SUCC(ptr), PRED(ptr) - SUCC(ptr));
			}
		}
	}
	else if (ptr_size <= 1024) {
		if (ptr == ptr_classes[1]) {
			ptr_classes[1] = GET(ptr + 4) == 0 ? NULL : SUCC(ptr);
		}
		else {
			if (GET(ptr + 4) == 0) {
				PUT(PRED(ptr) + 4, 0);
			}
			else {
				PUT(PRED(ptr) + 4, SUCC(ptr) - PRED(ptr));
				PUT(SUCC(ptr), PRED(ptr) - SUCC(ptr));
			}
		}
	}
	else if (ptr_size <= 2048) {
		if (ptr == ptr_classes[2]) {
			ptr_classes[2] = GET(ptr + 4) == 0 ? NULL : SUCC(ptr);
		}
		else {
			if (GET(ptr + 4) == 0) {
				PUT(PRED(ptr) + 4, 0);
			}
			else {
				PUT(PRED(ptr) + 4, SUCC(ptr) - PRED(ptr));
				PUT(SUCC(ptr), PRED(ptr) - SUCC(ptr));
			}
		}
	}
	else if (ptr_size <= 4096) {
		if (ptr == ptr_classes[3]) {
			ptr_classes[3] = GET(ptr + 4) == 0 ? NULL : SUCC(ptr);
		}
		else {
			if (GET(ptr + 4) == 0) {
				PUT(PRED(ptr) + 4, 0);
			}
			else {
				PUT(PRED(ptr) + 4, SUCC(ptr) - PRED(ptr));
				PUT(SUCC(ptr), PRED(ptr) - SUCC(ptr));
			}
		}
	}
	else if (ptr_size <= 8192) {
		if (ptr == ptr_classes[4]) {
			ptr_classes[4] = GET(ptr + 4) == 0 ? NULL : SUCC(ptr);
		}
		else {
			if (GET(ptr + 4) == 0) {
				PUT(PRED(ptr) + 4, 0);
			}
			else {
				PUT(PRED(ptr) + 4, SUCC(ptr) - PRED(ptr));
				PUT(SUCC(ptr), PRED(ptr) - SUCC(ptr));
			}
		}
	}
	else if (ptr_size <= 16384) {
		if (ptr == ptr_classes[5]) {
			ptr_classes[5] = GET(ptr + 4) == 0 ? NULL : SUCC(ptr);
		}
		else {
			if (GET(ptr + 4) == 0) {
				PUT(PRED(ptr) + 4, 0);
			}
			else {
				PUT(PRED(ptr) + 4, SUCC(ptr) - PRED(ptr));
				PUT(SUCC(ptr), PRED(ptr) - SUCC(ptr));
			}
		}
	}
	else{
		if (ptr == ptr_classes[6]) {
			ptr_classes[6] = GET(ptr + 4) == 0 ? NULL : SUCC(ptr);
		}
		else {
			if (GET(ptr + 4) == 0) {
				PUT(PRED(ptr) + 4, 0);
			}
			else {
				PUT(PRED(ptr) + 4, SUCC(ptr) - PRED(ptr));
				PUT(SUCC(ptr), PRED(ptr) - SUCC(ptr));
			}
		}
	}
}
/*Add a free block from its list.
 *The idea is like find_fit and delete_from_class:
 *according to the size of the block we want to free,
 *go to its corresponding list.
 *Depending on whether it is a head or foot or somewhere between,
 *change corresponding prev and succ.
 */

inline static void append_to_class(char* bp,int size) {
	if (size <= 512) {
		PUT(bp, 0);
		if (ptr_classes[0] != NULL) {
			PUT(bp + 4, ptr_classes[0] - bp);
			PUT(ptr_classes[0], bp - ptr_classes[0]);
		}
		else {
			PUT(bp + 4, 0);
		}
		ptr_classes[0] = bp;
	}
	else if (size <= 1024) {
		PUT(bp, 0);
		if (ptr_classes[1] != NULL) {
			PUT(bp + 4, ptr_classes[1] - bp);
			PUT(ptr_classes[1], bp - ptr_classes[1]);
		}
		else {
			PUT(bp + 4, 0);
		}
		ptr_classes[1] = bp;
	}
	else if (size <= 2048) {
		PUT(bp, 0);
		if (ptr_classes[2] != NULL) {
			PUT(bp + 4, ptr_classes[2] - bp);
			PUT(ptr_classes[2], bp - ptr_classes[2]);
		}
		else {
			PUT(bp + 4, 0);
		}
		ptr_classes[2] = bp;
	}
	else if (size <= 4096) {
		PUT(bp, 0);
		if (ptr_classes[3] != NULL) {
			PUT(bp + 4, ptr_classes[3] - bp);
			PUT(ptr_classes[3], bp - ptr_classes[3]);
		}
		else {
			PUT(bp + 4, 0);
		}
		ptr_classes[3] = bp;
	}
	else if (size <= 8192) {
		PUT(bp, 0);
		if (ptr_classes[4] != NULL) {
			PUT(bp + 4, ptr_classes[4] - bp);
			PUT(ptr_classes[4], bp - ptr_classes[4]);
		}
		else {
			PUT(bp + 4, 0);
		}
		ptr_classes[4] = bp;
	}
	else if (size <= 16384) {
		PUT(bp, 0);
		if (ptr_classes[5] != NULL) {
			PUT(bp + 4, ptr_classes[5] - bp);
			PUT(ptr_classes[5], bp - ptr_classes[5]);
		}
		else {
			PUT(bp + 4, 0);
		}
		ptr_classes[5] = bp;
	}
	else {
		PUT(bp, 0);
		if (ptr_classes[6] != NULL) {
			PUT(bp + 4, ptr_classes[6] - bp);
			PUT(ptr_classes[6], bp - ptr_classes[6]);
		}
		else {
			PUT(bp + 4, 0);
		}
		ptr_classes[6] = bp;
	}
}
