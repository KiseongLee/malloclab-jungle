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


team_t team = {
    /* Team name */
    "jungle",
    /* First member's full name */
    "Lee",
    /* First member's email address */
    "Lee@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
    };



/* Basic constants and macros */
#define WSIZE 4 /* Word and header/footer size (bytes) */
#define DSIZE 8 /* Double word size (bytes) */
#define CHUNKSIZE (1<<12) /* Extend heap by this amount (bytes) */

#define MAX(x, y) ((x) > (y)? (x) : (y))
/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

static void *coalesce(void *bp){
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size =  GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc){ // case 1 - 이전과 다음 블록이 모두 할당 되어있는 경우, 현재 블록의 상태는 할당에서 가용으로 변경
        return bp;
    }
    else if (prev_alloc && !next_alloc){ // case2 - 이전 블록은 할당 상태, 다음 블록은 가용상태. 현재 블록은 다음 블록과 통합 됨.
        size += GET_SIZE(HDRP(NEXT_BLKP(bp))); // 다음 블록의 헤더만큼 사이즈 추가?
        PUT(HDRP(bp),PACK(size,0)); // 헤더 갱신
        PUT(FTRP(bp), PACK(size,0)); // 푸터 갱신
    }
    else if(!prev_alloc && next_alloc){ // case 3 - 이전 블록은 가용상태, 다음 블록은 할당 상태. 이전 블록은 현재 블록과 통합. 
        size+= GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size,0)); 
        PUT(HDRP(PREV_BLKP(bp)), PACK(size,0)); // 헤더를 이전 블록의 BLKP만큼 통합?
        bp = PREV_BLKP(bp);
    }
    else { // case 4- 이전 블록과 다음 블록 모두 가용상태. 이전,현재,다음 3개의 블록 모두 하나의 가용 블록으로 통합.
        size+= GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp))); // 이전 블록 헤더, 다음 블록 푸터 까지로 사이즈 늘리기
        PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size,0));
        bp = PREV_BLKP(bp);
    }
    return bp;
}

static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1){
        return NULL;
    }
    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0)); /* Free block header */
    PUT(FTRP(bp), PACK(size, 0)); /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */

    /* Coalesce if the previous block was free */
    return coalesce(bp);
}

/* 
 * mm_init - initialize the malloc package.
 */
static char *heap_listp;

int mm_init(void)
{
    /* create 초기 빈 heap*/
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void*)-1){
        return -1;
    }
    PUT(heap_listp,0);                          /* Alignment padding */
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE,1)); /* Prologue header */
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE,1)); /* Prologue footer */
    PUT(heap_listp + (3*WSIZE), PACK(0,1));     /* Epilogue header */
    heap_listp+= (2*WSIZE);

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE)==NULL)
        return -1;
    return 0;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp){ 
    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp),PACK(size,0)); // header, footer 들을 free 시킨다.
    PUT(FTRP(bp), PACK(size,0));
    coalesce(bp);
}

static void *find_fit(size_t asize)
{
    /* First-fit search */
    void *bp;
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) { 
            // init에서 쓴 heap_listp를 쓴다. 처음 출발 후, 다음 block의 첫번 째 헤더 뒤 위치다.
            // for문이 계속 돌면 epilogue header까지 간다. epilogue header는 0이니까 종료된다.
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
         //이 블록이 가용하고(not 할당) 내가 갖고 있는 asize를 담을 수 있으면
          return bp; // 블록 위치 바로 리턴
        }
    }
    return NULL; /* No fit */

}

static void place(void *bp, size_t asize)
  // 들어갈 위치를 포인터로 받는다. (find fit에서 찾은 bp) 크기는 asize로 받음.
{
    size_t csize = GET_SIZE(HDRP(bp));
    // 현재 있는 블록 사이즈
    if ((csize - asize) >= (2*DSIZE)) {
        // 현재 블록 사이즈 안에서 asize를 넣어도 2*DSIZE(헤더와 풋터를 감안한 최소 사이즈)만큼 남으면
        // 다른 data를 넣을 수 있음
        PUT(HDRP(bp), PACK(asize, 1));
        // 헤더 위치에 asize만큼 넣고 1(alloc)로 상태 변환. 원래 헤더 사이즈에서 지금 넣으려고 하는 사이즈(asize)로 갱신.(자르는 효과)
        PUT(FTRP(bp), PACK(asize, 1));
        // 풋터 위치도 변경
        bp = NEXT_BLKP(bp);
        // regular block만큼 하나 이동해서 bp 위치 갱신
        PUT(HDRP(bp), PACK(csize-asize, 0));
        // 나머지 블록(csize-asize) 다 가용하다(0)하다라는 걸 다음 헤더에 표시
        PUT(FTRP(bp), PACK(csize-asize, 0));
        // 풋터에도 표시
    }
    else { // 현재 블록 사이즈 안에서 asize를 넣으면 2*DSIZE보다 작으면 분할할 필요 없음
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize; /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp;

    /* Ignore spurious requests */
    if (size == 0) return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE){
        asize = 2*DSIZE;
    }
    else{
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);
    }
    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize,CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL){
         return NULL;
    }
    place(bp, asize);
    return bp;
}
/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    
    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;
    copySize = GET_SIZE(HDRP(oldptr));  
    if (size < copySize)
      copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}














