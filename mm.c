/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "team_5",
    /* First member's full name */
    "park geon woo",
    /* First member's email address */
    "ceh20002@naver.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8
/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1<<12)

#define MAX(x, y)((x) > (y) ? (x) : (y))
#define PACK(size, alloc)((size) | (alloc))
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val)(*(unsigned int *)(p) = (val))

#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *next_fit(size_t asize);
static void place(void *bp, size_t asize);
void *mm_realloc(void *ptr, size_t size);

static char *mem_heap; // points to first byte of heap
static char *mem_brk; // poinsts to last byte of heap plus 1
static char *mem_max_addr; // max legalheap addr plus 1
static char *heap_listp = NULL;
static char *recent_allocate;

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *) -1) return -1;
    PUT(heap_listp, 0);
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE,1));
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE,1));
    PUT(heap_listp + (3*WSIZE), PACK(0,1));
    heap_listp += (2*WSIZE);

    if (extend_heap(CHUNKSIZE/WSIZE) == NULL){
        return - 1;
    }
    return 0;
}

/*
 * mm_free - Freeing a block does nothing.
 */

void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp;

    /* Ignore spurious requests */
    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)
        asize = 2*DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);

    /* Search the free list for a fit */
    if ((bp = next_fit(asize)) != NULL) {
        place(bp, asize);
        recent_allocate = bp;
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize,CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;

    place(bp, asize);
    recent_allocate = bp;
    return bp;
}

void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    
    // 케이스 1: 기존 포인터가 NULL인 경우
    // 이는 새로운 메모리 할당을 의미하므로, 단순히 malloc을 호출
    if (ptr == NULL)
        return mm_malloc(size);
    
    // 케이스 2: 요청한 크기가 0인 경우
    // 이는 메모리 해제를 의미하므로, free를 호출하고 NULL을 반환
    if (size == 0) {
        mm_free(ptr);
        return NULL;
    }
    
    // 새로운 크기로 메모리를 할당
    newptr = mm_malloc(size);
    // 메모리 할당에 실패한 경우 NULL을 반환
    if (newptr == NULL)
        return NULL;
    
    // 복사할 데이터의 크기를 결정
    // 기존 블록의 크기에서 헤더와 푸터의 크기(DSIZE)를 뺌
    copySize = GET_SIZE(HDRP(oldptr)) - DSIZE; 
    // 새로 요청한 크기가 기존 데이터 크기보다 작다면, 새 크기만큼만 복사
    if (size < copySize)
        copySize = size;
    
    // 기존 데이터를 새 위치로 복사
    memcpy(newptr, oldptr, copySize);
    // 기존 메모리를 해제합니다.
    mm_free(oldptr);
    // 새로 할당된 메모리의 포인터를 반환
    return newptr;
}

static void *extend_heap(size_t words){
    char *bp;
    size_t size;

    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1){
        return NULL;
    }

    PUT(HDRP(bp),PACK(size,0));
    PUT(FTRP(bp),PACK(size,0));
    PUT(HDRP(NEXT_BLKP(bp)),PACK(0,1));

    return coalesce(bp);
}

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {         /* Case 1 */
        return bp;
    }

    else if (prev_alloc && !next_alloc) {   /* Case 2 */
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    else if (!prev_alloc && next_alloc) {   /* Case 3 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    else {                                  /* Case 4 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    recent_allocate = bp;
    return bp;
} 

static void *next_fit(size_t asize){
    void *bp;
    if (recent_allocate == NULL){
        recent_allocate = heap_listp;
    }
    // GET_SIZE(HDRP(bp)) > 0로 블록 크기가 0보다 큰 동안 계속
    for (bp = recent_allocate; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))){
            recent_allocate = bp;
            return bp;
        }
    }
    return NULL;
}

// // 최소 크기는 2*DSIZE(일반적으로 16바이트)입니다.
static void place(void *bp, size_t asize){
    size_t csize = GET_SIZE(HDRP(bp));
    // 현재 블록의 크기에서 요청된 크기를 뺀 값이 최소 블록 크기(2*DSIZE)보다 크거나 같은지 확인합니다.
    // 이는 블록을 분할할 수 있는지 확인하는 조건입니다.
    // csize 는 현재 가용 블록의 전체 크기 asize 실제 할당될 블록의 크기(헤더 푸터 포함)
    if ((csize - asize) >= (2*DSIZE)){
        // 요청된 크기로 새 할당 블록의 헤더를 설정합니다.
        PUT(HDRP(bp), PACK(asize, 1));
        // 요청된 크기로 새 할당 블록의 푸터를 설정합니다.
        PUT(FTRP(bp), PACK(asize, 1));
        // 포인터를 다음 블록으로 이동합니다.
        bp = NEXT_BLKP(bp);
        // 남은 공간에 새 가용 블록의 헤더를 설정합니다.
        PUT(HDRP(bp), PACK(csize-asize , 0));
        // 남은 공간에 새 가용 블록의 푸터를 설정합니다.
        PUT(FTRP(bp), PACK(csize-asize, 0));
        // 만약 분할이 불가능하다면
    } else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}