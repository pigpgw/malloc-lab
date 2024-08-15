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
/* 메모리 할당기 구현 */

/* 단일 워드(4바이트) 또는 더블 워드(8바이트) 정렬 */
#define ALIGNMENT 8

/* 주어진 크기를 ALIGNMENT의 가장 가까운 배수로 올림 */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

/* size_t 타입의 크기를 정렬된 크기로 변환 */
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* 기본 상수 정의 */
#define WSIZE 4             /* 워드 크기 (바이트) */
#define DSIZE 8             /* 더블 워드 크기 (바이트) */
#define CHUNKSIZE (1<<12)   /* 힙을 이만큼 확장 (4096 바이트) */

/* 최대값을 구하는 매크로 */
#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* 크기와 할당 비트를 하나의 워드로 묶는 매크로 */
#define PACK(size, alloc) ((size) | (alloc))

/* 주소 p에서 워드를 읽고 쓰는 매크로 */
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* 주소 p의 헤더 또는 푸터에서 크기와 할당 비트를 읽어오는 매크로 */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* 블록 포인터 bp를 받아 그 블록의 헤더와 푸터의 주소를 계산하는 매크로 */
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* 블록 포인터 bp를 받아 이전 블록과 다음 블록의 주소를 계산하는 매크로 */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* 함수 선언 */
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *next_fit(size_t asize);
static void place(void *bp, size_t asize);
void *mm_realloc(void *ptr, size_t size);

/* 전역 변수 */
static char *mem_heap;      /* 힙의 첫 바이트를 가리키는 포인터 */
static char *mem_brk;       /* 힙의 마지막 바이트 다음을 가리키는 포인터 */
static char *mem_max_addr;  /* 최대 합법적인 힙 주소 다음을 가리키는 포인터 */
static char *heap_listp = NULL;  /* 프롤로그 블록을 가리키는 포인터 */
static char *recent_allocate;    /* 최근 할당된 블록을 가리키는 포인터 (next_fit 알고리즘용) */

/* 
 * mm_init - malloc 패키지를 초기화합니다.
 */
int mm_init(void)
{
    /* 초기 빈 힙 생성 */
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *) -1) 
        return -1;
    PUT(heap_listp, 0);                             /* 정렬 패딩 */
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));    /* 프롤로그 헤더 */
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));    /* 프롤로그 푸터 */
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));        /* 에필로그 헤더 */
    heap_listp += (2*WSIZE);

    /* CHUNKSIZE 바이트의 빈 공간으로 힙 확장 */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    return 0;
}

/*
 * mm_free - 블록을 해제하고 인접한 가용 블록들과 병합합니다.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

/* 
 * mm_malloc - 요청된 크기의 메모리 블록을 할당합니다.
 *     항상 정렬의 배수인 크기의 블록을 할당합니다.
 */
void *mm_malloc(size_t size)
{
    size_t asize;      /* 조정된 블록 크기 */
    size_t extendsize; /* 힙 확장 크기 (적합한 블록이 없을 경우) */
    char *bp;

    /* 유효하지 않은 요청 무시 */
    if (size == 0)
        return NULL;

    /* 오버헤드와 정렬 요구사항을 포함하여 블록 크기 조정 */
    if (size <= DSIZE)
        asize = 2*DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);

    /* 적합한 가용 블록을 찾아 할당 */
    if ((bp = next_fit(asize)) != NULL) {
        place(bp, asize);
        recent_allocate = bp;
        return bp;
    }

    /* 적합한 블록을 찾지 못한 경우, 힙을 확장하고 블록 할당 */
    extendsize = MAX(asize,CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    recent_allocate = bp;
    return bp;
}

/*
 * mm_realloc - 이미 할당된 메모리 블록의 크기를 조정합니다.
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    
    // 케이스 1: ptr가 NULL인 경우, 새 메모리를 할당
    if (ptr == NULL)
        return mm_malloc(size);
    
    // 케이스 2: size가 0인 경우, 메모리를 해제
    if (size == 0) {
        mm_free(ptr);
        return NULL;
    }
    
    // 새로운 크기로 메모리를 할당 
    newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;
    
    // 복사할 데이터의 크기를 결정 (헤더와 푸터 제외)
    copySize = GET_SIZE(HDRP(oldptr)) - DSIZE;
    if (size < copySize)
        copySize = size;
    
    // 데이터를 새 위치로 복사
    memcpy(newptr, oldptr, copySize);
    // 이전 메모리 해제
    mm_free(oldptr);
    return newptr;
}


/*
 * extend_heap - 워드 단위의 메모리로 힙을 확장하고 초기화합니다.
 */
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    /* 더블 워드 정렬을 유지하기 위해 크기를 조정 */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    /* 새 가용 블록의 헤더/푸터와 에필로그 헤더를 초기화 */
    PUT(HDRP(bp), PACK(size, 0));         /* 가용 블록 헤더 */
    PUT(FTRP(bp), PACK(size, 0));         /* 가용 블록 푸터 */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* 새 에필로그 헤더 */

    /* 이전 블록이 가용하다면 병합 */
    return coalesce(bp);
}

/*
 * coalesce - 경계 태그 연결을 사용하여 가용 블록을 병합합니다.
 */
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

     /* 케이스 1: 이전과 다음 블록이 모두 할당된 경우 */
    if (prev_alloc && next_alloc) {        
        return bp;
    }
     /* 케이스 2: 이전 블록은 할당되고 다음 블록은 가용한 경우 */
    else if (prev_alloc && !next_alloc) {  
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    /* 케이스 3: 이전 블록은 가용하고 다음 블록은 할당된 경우 */
    else if (!prev_alloc && next_alloc) {   
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    /* 케이스 4: 이전과 다음 블록이 모두 가용한 경우 */
    else {                                  
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    recent_allocate = bp;
    return bp;
}

/*
 * next_fit - 최근 할당된 블록부터 시작하여 적합한 가용 블록을 찾음
 */
static void *next_fit(size_t asize)
{
    void *bp;
    
    /* 처음 호출 시 recent_allocate 초기화 */
    if (recent_allocate == NULL) {
        recent_allocate = heap_listp;
    }
    
    /* 최근 할당 위치부터 힙의 끝까지 검색 */
    for (bp = recent_allocate; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
            recent_allocate = bp;
            return bp;
        }
    }
    
    /* 적합한 블록을 찾지 못한 경우 NULL 반환 */
    return NULL;
}

//  place - 요청한 블록을 가용 블록의 시작 부분에 배치하고, 나머지 부분의 크기가 최소 블록 크기와 같거나 크다면 분할
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));

    if ((csize - asize) >= (2*DSIZE)) {
        /* 요청한 블록을 배치 */
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        /* 남은 부분에 새 가용 블록 생성 */
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));
    }
    else {
        /* 분할하지 않고 전체 블록을 사용 */
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}