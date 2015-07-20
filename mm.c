/*
 * mm.c
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
#define DEBUG
#ifdef DEBUG
# define dbg_printf(...) printf(__VA_ARGS__)
#else
# define dbg_printf(...)
#endif


/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(p) (((size_t)(p) + (ALIGNMENT-1)) & ~0x7)


/*Start editting from this on */


#define WSIZE       4        /* Word and header/footer size (bytes) */ 
#define DSIZE       8       /* Double word size (bytes) */
#define CHUNKSIZE  (1<<12)   /* Extend heap by this amount (bytes) */  
#define NUM_OF_LIST 14    
                        /*The size of free list from 2^4 to 2^17*/
#define WNULL 0U

#define MAX(x, y) ((x) > (y)? (x) : (y))  

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc)) 

/* Read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p))            
#define PUT(p, val)  (*(unsigned int *)(p) = (val))    

/* Read and write the pointer at address p*/  
#define PUT_PTR(p, ptr)  (* (void **)(p) = ptr) 
#define GET_PTR(p)       (* (void **)(p))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)         (GET(p) & ~0x7)                   
#define GET_ALLOC(p)        (GET(p) & 0x1)       
#define GET_PREV_ALLOC(p)   (GET(p) & 0x2)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)                      
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) 

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) 
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) 

#define GET_PREV(bp)    (GET_PTR(bp)) 
#define GET_NEXT(bp)    (GET_PTR((void *)bp + DSIZE)) 
#define SET_NEXT(bp, ptr)       (PUT_PTR((void*)bp + DSIZE, ptr)) 
#define SET_PREV(bp, ptr)       (PUT_PTR((void*)bp , ptr)) 

/*Global variables*/ 
static char *heap_listp = 0 ;  /* Pointer to first block */  
static char *heap_ptr_head = 0 ; 

static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
// static void printblock(void *bp); 
static void checkheap(int verbose);
static void *add_to_list(void *bp, size_t size) ; 
static void *delete_block_from_list(void *bp, size_t size) ; 
static int in_heap(const void *p); 
static int aligned(const void *p); 
static void printblock(void *bp) ;
static void checkblock(void *bp) ; 


static void* word_to_ptr(unsigned int w)  
{  
    return ((w) == WNULL ? NULL : (void*)((unsigned int)(w) + 0x800000000UL));  
}  

static unsigned int ptr_to_word(void* p)  
{  
    return ((p) == NULL ? WNULL : (unsigned int)((unsigned long)(p) - 0x800000000UL));  
}  


/*
 * Initialize: return -1 on error, 0 on success.
 */
int mm_init(void) {
    int i = 0 ; 

    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(4 * WSIZE + NUM_OF_LIST * WSIZE)) == (void *)-1) //line:vm:mm:begininit
        return -1;

    heap_ptr_head = heap_listp ; 

    PUT(heap_listp + NUM_OF_LIST * WSIZE, 0);                          /* Alignment padding */
    PUT(heap_listp + (1*WSIZE) + NUM_OF_LIST * WSIZE, PACK(DSIZE, 1)); /* Prologue header */ 
    PUT(heap_listp + (2*WSIZE) + NUM_OF_LIST * WSIZE, PACK(DSIZE, 1)); /* Prologue footer */ 
    PUT(heap_listp + (3*WSIZE) + NUM_OF_LIST * WSIZE, PACK(0, 1));     /* Epilogue header */
    /* $end mminit */  

    for (i = 0 ; i < NUM_OF_LIST ; i++ ){
        PUT_PTR(heap_ptr_head + i * WSIZE, 0) ; 
    }

    heap_listp += (NUM_OF_LIST * WSIZE + 2 * WSIZE ) ; 

    // checkheap(0) ; 

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) 
        return -1; 
    // checkheap(0) ; 
    return 0;
}

/*
 * malloc
 */
void *malloc (size_t size) {
    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp;      
    // checkheap(0) ; 

    if (heap_listp == 0){
        mm_init();
    }
    /* $begin mmmalloc */
    /* Ignore spurious requests */
    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)
        asize = 3*DSIZE;   // Header + footer (DSIZE) + Data & Alignment(DSIZE) + PREV & SUCC (DSIZE)
    else
        asize = ALIGN(DSIZE + size) ;  // Properly use the function that is given by the example.

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {  
        place(bp, asize);         
        // checkheap(0) ; 
        return bp;
    }

    /* No fit found. Get more memory and place the block */

    extendsize = MAX(asize,CHUNKSIZE);                 
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)  
        return NULL;                                  
    place(bp, asize);
    // checkheap(0) ;
    return bp;
}

/*
 * free
 */
void free (void *ptr) {

    if(!ptr) return; 

    size_t size = GET_SIZE(HDRP(ptr)) ; 

    if (heap_listp == 0){
        mm_init();
    }

    PUT(HDRP(ptr), PACK(size, 0)) ;
    PUT(FTRP(ptr), PACK(size, 0)) ;
    void* bp = coalesce(ptr) ; 
    add_to_list(bp, GET_SIZE(HDRP(bp))) ; 

}

/*
 * realloc - you may want to look at mm-naive.c
 * In fact this function directly use the one in mm-naive.c
 */
void *realloc(void *oldptr, size_t size) {

    size_t oldsize;
    void *newptr;

    if(size == 0){
        free(oldptr);
        return 0;
    }
    if(oldptr == NULL) {
        return malloc(size);
    }
    newptr = malloc(size);

      /* If realloc() fails the original block is left untouched  */
    if(!newptr){
        return 0;
    }

    /* Copy the old data. */
    oldsize = GET_SIZE(HDRP(oldptr));

    if(size < oldsize) oldsize = size;
    memcpy(newptr, oldptr, oldsize);

    /* Free the old block. */
    free(oldptr);

    return newptr;
}

/*
 * calloc - you may want to look at mm-naive.c
 * This function is not tested by mdriver, but it is
 * needed to run the traces.
 */
void *calloc (size_t nmemb, size_t size) {
    // Remain the same with the implementation in mm-naive.c 
    size_t bytes = nmemb * size;
    void *newptr;

    newptr = malloc(bytes);
    memset(newptr, 0, bytes);

    return newptr;
}


/*
 * Return whether the pointer is in the heap.
 * May be useful for debugging.
 */
static int in_heap(const void *p) {
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}

/*
 * Return whether the pointer is aligned.
 * May be useful for debugging.
 */
static int aligned(const void *p) {
    return (size_t)ALIGN(p) == (size_t)p;
}

/*
 * mm_checkheap
 */
void mm_checkheap(int lineno) {
    checkheap(1);
}




static void *coalesce(void *bp) 
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {            /* Case 1 */
        return bp;
    }

    else if (prev_alloc && !next_alloc) {      /* Case 2 */
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));

        delete_block_from_list(NEXT_BLKP(bp), GET_SIZE(HDRP(NEXT_BLKP(bp)))) ; 

        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    else if (!prev_alloc && next_alloc) {      /* Case 3 */
        // size += GET_SIZE(HDRP(PREV_BLKP(bp)));

        // delete_block_from_list(PREV_BLKP(bp), GET_SIZE(HDRP(PREV_BLKP(bp)))) ; 

        // PUT(FTRP(bp), PACK(size, 0));
        // PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        // bp = PREV_BLKP(bp);
        bp = PREV_BLKP(bp);
        size += GET_SIZE(HDRP(bp));

        delete_block_from_list(bp, GET_SIZE(HDRP(bp)));

        PUT(HDRP(bp), PACK(size,0));
        PUT(FTRP(bp), PACK(size,0));
    }

    else {                                     /* Case 4 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + 
            GET_SIZE(FTRP(NEXT_BLKP(bp)));

        delete_block_from_list(PREV_BLKP(bp), GET_SIZE(HDRP(PREV_BLKP(bp))) ) ; 
        delete_block_from_list(NEXT_BLKP(bp), GET_SIZE(HDRP(NEXT_BLKP(bp))) ) ;

        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));

        bp = PREV_BLKP(bp);
    }
    // checkheap(0) ; 
    return bp;
}


static void *extend_heap(size_t words) 
{
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE; 
    if ((long)(bp = mem_sbrk(size)) == -1)  
        return NULL;                                        

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));         /* Free block header */   
    PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */   

    SET_NEXT(bp, NULL) ; 
    SET_PREV(bp, NULL) ; 

    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */ 

    /* Coalesce if the previous block was free */
    bp = coalesce(bp);
    add_to_list(bp, GET_SIZE(HDRP(bp)));
    // checkheap(0) ; 
    return bp ;
} 


int size_map(size_t size)
{
    int offset ; 

    if (size < (1<<4)) 
        offset = 0 ;  
    else if (size < (1<<5)) 
        offset = 1 ;  
    else if (size < (1<<6)) 
        offset = 2 ; 
    else if (size < (1<<7)) 
        offset = 3 ; 
    else if (size < (1<<8)) 
        offset = 4 ; 
    else if (size < (1<<9)) 
        offset = 5 ; 
    else if (size < (1<<10)) 
        offset = 6 ; 
    else if (size < (1<<11)) 
        offset = 7 ; 
    else if (size < (1<<12)) 
        offset = 8 ; 
    else if (size < (1<<13)) 
        offset = 9 ;  
    else if (size < (1<<14)) 
        offset = 10 ; 
    else if (size < (1<<15)) 
        offset = 11 ; 
    else if (size < (1<<16)) 
        offset = 12 ; 
    else offset = 13 ; 

    return offset ; 
}


/*
    Here is the logic of block: When one block is ready to be added into the list,
    All of its properties should be set properly already, including
    header, footer, other bit etc. 
    Hold this principles all through the programs and prevent the uncertainty 
    messy you program.
*/

/* Add the free block into the head of proper list */
static void *add_to_list(void *bp, size_t size) 
{   
    void *target_position = heap_ptr_head + size_map(size) * WSIZE  ; 
    // void *original_head_bp = GET_PTR(target_position) ; 
    void *original_head_bp = word_to_ptr(GET(target_position)) ; 

    /*
    * Put the bp in the target position as the list head
    */
    // PUT_PTR(target_position, bp) ;  
    PUT(target_position, ptr_to_word(bp)) ; 

    SET_PREV(bp, NULL) ;            
    if (original_head_bp != NULL) {        
        SET_NEXT(bp, original_head_bp) ; 
        SET_PREV(original_head_bp, bp) ;  
    } 
    else {
        SET_NEXT(bp, NULL);
    }
    return bp ; 
}

// If a block starting from bp is alloced, just delete it from the owning list.
static void *delete_block_from_list(void *bp, size_t size) 
{

    void* next_block = GET_NEXT(bp) ; 
    void* prev_block = GET_PREV(bp) ;  

    if (next_block == NULL  && prev_block == NULL){
        // This is the only block ptr in this list 
        void *target_position =  heap_ptr_head + size_map(size) * WSIZE ;  
        // PUT_PTR(target_position, NULL) ; 
        PUT(target_position , 0 ) ; 
    }
    else if (next_block == NULL && prev_block != NULL){
        SET_NEXT(prev_block, NULL) ; 
    }
    else if (next_block != NULL && prev_block == NULL){
        void *target_position =  heap_ptr_head + size_map(size) * WSIZE ;  
        // PUT_PTR(target_position, next_block) ;  
        PUT(target_position, ptr_to_word(next_block)) ; 
        SET_PREV(next_block, NULL) ; 
    }
    else if (next_block != NULL && prev_block != NULL){
        SET_NEXT(prev_block, next_block) ; 
        SET_PREV(next_block, prev_block) ; 
    }
    // checkheap(0) ; 
    return bp ; 
}

static void *find_fit(size_t asize)
{
    // Calculate which list should it refer to search 
    int iter ; 
    void *bp = 0 ;
    //  Here you need to find out the method for initializing the value of pointer
    void *target_position = 0 ;    
    void *header_block_ptr = 0 ; 

    for (iter = size_map(asize) ; iter < NUM_OF_LIST ; iter ++ ){
        target_position = heap_ptr_head + iter * WSIZE ;
        // header_block_ptr = GET_PTR(target_position) ; 
        header_block_ptr = word_to_ptr(GET(target_position)) ; 

        if (header_block_ptr != NULL){
            for (bp = header_block_ptr; GET_SIZE(HDRP(bp)) > 0, bp != NULL; bp = GET_NEXT(bp)) {
                if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {      
                    // checkheap(0) ; 
                    return bp;
                }
            }
        }
        
    }
    // checkheap(0) ; 
    return NULL; 
}


static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));   

    delete_block_from_list(bp, csize) ;  


    if ((csize - asize) >= (3*DSIZE)) { 
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));  
        SET_NEXT(bp, NULL); 
        SET_PREV(bp, NULL); 

        bp = NEXT_BLKP(bp);   
        PUT(HDRP(bp), PACK(csize-asize, 0));        
        PUT(FTRP(bp), PACK(csize-asize, 0));

        add_to_list(bp, csize-asize) ;   
    }
    else { 
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
    // checkheap(0) ; 
}

/* 
 * checkheap - Minimal check of the heap for consistency 
 */
void checkheap(int lineno) 
{
    char *bp = heap_listp;

    if (lineno)
        printf("Heap (%p):\n", heap_listp);

    if ((GET_SIZE(HDRP(heap_listp)) != DSIZE) || !GET_ALLOC(HDRP(heap_listp)))
        printf("Bad prologue header\n");
    checkblock(heap_listp);

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (lineno) 
            printblock(bp);
        checkblock(bp);
    }

    if (lineno)
        printblock(bp);
    if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp))))
        printf("Bad epilogue header\n");
}


static void printblock(void *bp) 
{
    size_t hsize, halloc, fsize, falloc;

    checkheap(0);
    hsize = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp));  
    fsize = GET_SIZE(FTRP(bp));
    falloc = GET_ALLOC(FTRP(bp));  

    if (hsize == 0) {
        printf("%p: EOL\n", bp);
        return;
    }

    printf("%p: header: [%ld:%c] footer: [%ld:%c]\n", bp, 
           hsize, (halloc ? 'a' : 'f'), 
           fsize, (falloc ? 'a' : 'f')); 
}

static void checkblock(void *bp) 
{
    if ((size_t)bp % 8)
        printf("Error: %p is not doubleword aligned\n", bp);
    if (GET(HDRP(bp)) != GET(FTRP(bp)))
        printf("Error: header does not match footer\n");
}


static void check_free_list(size_t size)
{
    void *target_position = heap_ptr_head + size_map(size) * DSIZE  ; 
    void *original_head_bp = GET_PTR(target_position) ; 
    void *tmp = original_head_bp ;  
    int length = 0 ; 
    
    while(tmp != NULL){
        checkblock(original_head_bp) ; 
        tmp = GET_NEXT(tmp) ; 
        length += 1 ; 
    }
}

