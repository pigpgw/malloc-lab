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

/* 블록의 크기를 가져옵니다. 하위 3비트를 마스킹하여 제거합니다.
   이는 크기가 8의 배수이며, 하위 3비트가 다른 정보를 저장하는 데 사용되기 때문입니다. */
#define GET_SIZE(p) (GET(p) & ~0x7)

/* 블록의 할당 상태를 가져옵니다. 최하위 비트가 1이면 할당된 상태, 0이면 가용 상태입니다. */
#define GET_ALLOC(p) (GET(p) & 0x1)

/* 주어진 블록 포인터(bp)에서 해당 블록의 헤더 포인터를 계산합니다.
   bp에서 WSIZE(워드 크기)만큼 뒤로 가면 헤더 위치가 됩니다. */
#define HDRP(bp) ((char *)(bp) - WSIZE)

/* 주어진 블록 포인터(bp)에서 해당 블록의 푸터 포인터를 계산합니다.
   bp에 블록 크기를 더하고 DSIZE(더블 워드 크기)를 빼면 푸터 위치가 됩니다. */
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* 현재 블록의 다음 블록 포인터를 계산합니다.
   현재 블록의 크기만큼 앞으로 이동하면 다음 블록의 시작점이 됩니다. */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))

/* 현재 블록의 이전 블록 포인터를 계산합니다.
   이전 블록의 푸터에서 크기를 읽어 그만큼 뒤로 이동합니다. */
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
void *mm_realloc(void *ptr, size_t size);

static char *mem_heap; // points to first byte of heap
static char *mem_brk; // poinsts to last byte of heap plus 1
static char *mem_max_addr; // max legalheap addr plus 1
static char *heap_listp = NULL;

int mm_init(void)
{
    // 빈 힙 생성
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *) -1) return -1;
    // 첫 번째 워드를 0으로 더블 워드 경계로 정렬된 미사용 패딩 워드임, 패딩 다음에는 특별한 프롤로그 prolog 블록이 오며, 이것은 헤더와 풋터로만 구성된 8바이트 할당 블록
    // 프롤로그 블록은 초기화 과정에서 생성되며 절대 반환하지 않는다. 프롤로그 블록 다음에는 malloc 또는 free를 호출해서 생성된 0또는 1개 이상의 일반 블록들이 온다. 
    // 힙은 항상 특별한 에필로그 블록으로 끝나며, 이것은 헤더 만드로 구성된 크디가 0으로 할당된 블록이다.
    // 프롤로그와 에필로그 블록들은 연결과정 동안에 가장자리 조건을 없애주기 위한 속임수다. 할당기는 한 개의 정적 전역 변수를 사용하며, 이것은 항상 프롤로그 블록을 가르킨다.
    // 작은 최적화로 프롤로그 블록 대신에 다음 블록을 가리키게 할 수 있다.
    PUT(heap_listp, 0);
     // 두 번째 워드에 프롤로그 헤더를 설정합니다. PACK(DSIZE,1)는 크기가 DSIZE(더블 워드 크기, 보통 8바이트)이고 할당된 상태(1)임을 나타냅니다.
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE,1));
    // 세 번째 워드에 프롤로그 푸터를 설정합니다. 헤더와 동일한 값을 가집니다.
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE,1));
    // 네 번째 워드에 에필로그 헤더를 설정합니다. 크기 0, 할당 상태 1을 나타냅니다. 
    PUT(heap_listp + (3*WSIZE), PACK(0,1)); 
     // heap_listp를 프롤로그 블록 다음으로 이동시킵니다., 이제 첫 번째 가용 블록을 가리키게 됩니다.
    heap_listp += (2*WSIZE);
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL){
        return - 1;
    }
    return 0;
}


static void *extend_heap(size_t words){
    char *bp;
    size_t size;
    // 요청된 워드 수가 홀수인 경우, 짝수로 만들어 8바이트 정렬을 보장 
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    // mem_sbrk(size)를 호출하여 힙을 확장 실패시 -1을 반환하므로, 이후 NULL을 반환하고 함수를 종료함
    if ((long)(bp = mem_sbrk(size)) == -1){
        return NULL;
    }
    // 블록의 헤더 위치를 계산
    PUT(HDRP(bp),PACK(size,0));
    // PACK(size, 0)은 블록 크기와 할당 상태(0 = 가용)을 패키징 합니다.)
    PUT(FTRP(bp),PACK(size,0));
    // PUT은 계산된 값을 헤더에 저장
    PUT(HDRP(NEXT_BLKP(bp)),PACK(0,1));

    return coalesce(bp);
}

void mm_free(void *bp)
{   
    // GET_SIZE를 통해 헤더에서 블록의 크기를 읽어옴
    size_t size = GET_SIZE(HDRP(bp));

    // 블록의 해더를 업테이트 함 PACK(HDRP(bp), PACK(size, 0));을 통해 블록의 크기와 할당 상태를 가용 가능으로 바꿔줌
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}


void *mm_malloc(size_t size)
{
    // 오버헤드와 정렬 오구사항을 고려한 조정된 블록 크기
    size_t asize; 
    // 적합한 블록을 찾지 못했을 때 힙을 확장한 크기
    size_t extendsize;
    // 블록 포인터로, 할당된 메모리 블록을 가리킴
    char *bp;

    // 요청의 크기가 0인 경우, NULL을 반환하여 요청을 무시
    if (size == 0) return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)
        asize = 2*DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize,CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

// size는 실제 paload 크기
void *mm_realloc(void *ptr, size_t size)
{
    size_t old_size = GET_SIZE(HDRP(ptr));
    size_t new_size = size + (2 * WSIZE);

    if (new_size <= old_size){
        return ptr;
    }
    else {
        size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(ptr)));
        size_t current_size = old_size + GET_SIZE(HDRP(NEXT_BLKP(ptr)));

        if (!next_alloc && current_size >= new_size){
            PUT(HDRP(ptr), PACK(current_size, 1));
            PUT(FTRP(ptr), PACK(current_size, 1));
            return ptr;
        }
        else {
            void *new_bp = mm_malloc(new_size);
            place(new_bp, new_size);
            memcpy(new_bp, ptr, new_size);
            mm_free(ptr);
            return new_bp;
        }
    }
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
    return bp;
}

static void *find_fit(size_t asize){
    void *bp;

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))){
            return bp;
        }
    }
    return NULL;
}

static void place(void *bp, size_t asize){
    size_t csize = GET_SIZE(HDRP(bp));

    if ((csize - asize) >= (2*DSIZE)){
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize , 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));
    } else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}










