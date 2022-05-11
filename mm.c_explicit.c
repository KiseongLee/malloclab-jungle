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

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

/* 메모리 할당 시 기본적으로 header와 footer를 위해 필요한 더블워드만큼의 메모리 크기 */
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* Basic constants and macros */
#define WSIZE 4 /* Word and header/footer size (bytes) */
#define DSIZE 8 /* Double word size (bytes) */
#define MINIMUM 16 /* Initial Prologue block size, header, footer, PREC, SUCC */
#define CHUNKSIZE (1<<12) /* Extend heap by this amount : 4096bytes -> 4k(bytes) */

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
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) // (char*)(bp) + GET_SIZE(지금 블록의 헤더값)
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) // (char*)(bp) - GET_SIZE(이전 블록의 풋터값)

/* Free List 상에서의 이전, 이후 블록의 포인터를 리턴한다. */
#define PREC_FREEP(bp) (*(void**)(bp))          // 이전 블록의 bp
#define SUCC_FREEP(bp) (*(void**)(bp + WSIZE))  // 이후 블록의 bp

/* define searching method for find suitable free blocks to allocate*/

/* global variable & functions */
static char* heap_listp = NULL; // 항상 prologue block을 가리키는 정적 전역 변수 설정
static char* free_listp = NULL; // free list의 맨 첫 블록을 가리키는 포인터

static void* extend_heap(size_t words);
static void* coalesce(void* bp);
static void* find_fit(size_t asize);
static void place(void* bp, size_t newsize);

int mm_init(void);
void *mm_malloc(size_t size);
void mm_free(void *bp);
void *mm_realloc(void *ptr, size_t size);

/* 
 * mm_init - initialize the malloc package.
 */

int mm_init(void)
{

    /* 메모리에서 6words를 가져오고 이걸로 빈 가용 리스트 초기화 */
     /* padding, prol_header, prol_footer, PREC, SUCC, epil_header */
    if ((heap_listp = mem_sbrk(6*WSIZE)) == (void*)-1){
        return -1;
    }
    PUT(heap_listp,0);                          /* Alignment padding */
    PUT(heap_listp + (1*WSIZE), PACK(MINIMUM,1)); /* Prologue header */
    PUT(heap_listp + (2*WSIZE), NULL); // prologue block안의 PREC 포인터 NULL로 초기화
    PUT(heap_listp + (3*WSIZE), NULL); // prologue block안의 SUCC 포인터 NULL로 초기화
    PUT(heap_listp + (4*WSIZE), PACK(MINIMUM,1));  /* Prologue footer */
    PUT(heap_listp + (5*WSIZE), PACK(0,1));     /* Epilogue header */
    
    free_listp = heap_listp + 2*WSIZE; //free_listp를 탐색의 시작점으로 둔다

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    // 그 후 CHUNKSIZE만큼 힙을 확장해 초기 가용 블록을 생성한다
    if (extend_heap(CHUNKSIZE/WSIZE)==NULL)
        return -1;
    return 0;
}

// coalesce(bp) : 해당 가욕 블록을 앞뒤 가용 블록과 연결하고 연결된 가용 블록의 주소를 리턴한다.

static void *coalesce(void *bp){
    // 직전 블록의 footer, 직후 블록의 header를 보고 가용 여부 확인
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); // 앞 블록 가용 여부
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // 뒷 블록 가용 여부
    size_t size =  GET_SIZE(HDRP(bp));

    // Case 1 : 앞, 뒷 블록 모두 할당 -> 해당 블록만 free list에 넣어준다
    
    // Case 2 : 앞 블록 할당, 뒷 블록 가용
    if (prev_alloc && !next_alloc){ 
        removeBlock(NEXT_BLKP(bp)); // free 상태였던 뒷 블록 free list에서 제거
        size += GET_SIZE(HDRP(NEXT_BLKP(bp))); // 다음 블록의 헤더만큼 사이즈 추가
        PUT(HDRP(bp),PACK(size,0)); // 헤더 갱신
        PUT(FTRP(bp), PACK(size,0)); // 푸터 갱신
    }
    //Case 3 : 앞 블록 가용, 뒷 블록 할당
    else if(!prev_alloc && next_alloc){  
        removeBlock(PREV_BLKP(bp)); // free 상태였던 앞 블록 free list에서 제거
        size+= GET_SIZE(HDRP(PREV_BLKP(bp))); // 이전 블록의 헤더만큼 사이즈 추가
        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0)); 

    }
    //Case 4 : 앞 블록 가용, 뒷 블록 가용
    else if(!prev_alloc && !next_alloc) { 
        removeBlock(NEXT_BLKP(bp)); // free 상태였던 뒷 블록 free list에서 제거
        removeBlock(PREV_BLKP(bp)); // free 상태였던 앞 블록 free list에서 제거
        size+= GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp))); // 이전 블록 헤더, 다음 블록 푸터 까지로 사이즈 늘리기
        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0)); 
        
        
    }
    // 연결된 새 가용 블록을 free list에 추가한다
    putFreeBlock(bp);

    return bp;
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
    // 할당 공간의 크기를 구하는 과정
    // DSIZE 보다 작으면 Alignment 요구사항에 의해서 asize는 4word가 된다(헤더 풋터 포함)
    if (size <= DSIZE){
        asize = 2*DSIZE;
    }
    // DSIZE보다 크면 가장 적합한 asize를 구해야한다.
    // 8의 배수에 맞춰주기 위해서 아래와 같은 식이 필요함
    // DSIZE = 헤더 + 풋터(2word)
    // DSIZE - 1 = 8의 배수를 만들기 위한 값 (7만큼을 더해주면 무조건 몫이 1이 증가하고 버림을 통해서 8의 배수를 맞춰줌)
    // DSIZE로 나누고 곱하면 가장 적합한 8의 배수가 나옴
    else{
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);
    }
    /* Search the free list for a fit */
    // asize에 맞는 크기를 가용 블록에서 찾으면 place 함수를 통해 할당
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    // 맞는 크기의 가용 블록이 없다면 새로 힙을 늘려서 새 힙에 메모리를 할당한다.
    extendsize = MAX(asize,CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL){
         return NULL;
    }
    place(bp, asize);
    return bp;
}

/* 
    extend_heap : 워드 단위 메모리를 인자로 받아 힙을 늘려준다
*/
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE; // size를 짝수 word && byte 형태로 만듬.
    if ((long)(bp = mem_sbrk(size)) == -1){ // 새 메모리의 첫 부분을 bp로 둔다. 주소값은 int로는 못받아서 long으로 casting함.
        return NULL;
    }
    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0)); /* Free block header */
    PUT(FTRP(bp), PACK(size, 0)); /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */

    /* Coalesce if the previous block was free */
    return coalesce(bp);
}

static void *find_fit(size_t asize)
{
    /* First-fit search */
    void *bp;
    // free list에서 가용 블럭을 차례로 확인한다. 맨 뒤의 프롤로그 블록이 유일하게 할당되었으므로 만나면 탐색 종료 
    for (bp = free_listp; GET_ALLOC(HDRP(bp)) != 1; bp = SUCC_FREEP(bp)) { 
            
        if (asize <= GET_SIZE(HDRP(bp))) {
         //이 블록이 내가 갖고 있는 asize를 담을 수 있으면
          return bp; // 블록 위치 바로 리턴
        }
    }
    return NULL; /* No fit */

}




/*
    place(bp, size) : 할당할 수 있는 free 블록을 free list에서 없애준다.
    할당 후 만약 분할이 되었다면, 새 가용 리스트를 free list에 넣어준다.

*/

static void place(void *bp, size_t asize)
  // 들어갈 위치를 포인터로 받는다. (find fit에서 찾은 bp) 크기는 asize로 받음.
{
    size_t csize = GET_SIZE(HDRP(bp));
    // 현재 있는 블록 사이즈

    removeBlock(bp);
    
    if ((csize - asize) >= (2*DSIZE)) {
        // 현재 블록 사이즈 안에서 asize를 넣어도 2*DSIZE(헤더와 풋터를 감안한 최소 사이즈)만큼 남으면
        // 다른 data를 넣을 수 있음
        PUT(HDRP(bp), PACK(asize, 1));
        // 헤더 위치에 asize만큼 넣고 1(alloc)로 상태 변환. 원래 헤더 사이즈에서 지금 넣으려고 하는 사이즈(asize)로 갱신.(자르는 효과)
        PUT(FTRP(bp), PACK(asize, 1));
        // 풋터도 변경
        bp = NEXT_BLKP(bp);
        // regular block만큼 하나 이동해서 bp 위치 갱신
        PUT(HDRP(bp), PACK(csize-asize, 0));
        // 나머지 블록(csize-asize) 다 가용하다(0)하다라는 걸 다음 헤더에 표시
        PUT(FTRP(bp), PACK(csize-asize, 0));
        // 풋터에도 표시

        putFreeBlock(bp);
        // free list 첫번째에 분할된 블럭을 넣는다.
    }
    else { // 현재 블록 사이즈 안에서 asize를 넣으면 2*DSIZE보다 작으면 분할할 필요 없음
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/*
    putFreeBlock(bp) : 새로 반환되거나 생성된 가용 블록을 free list의 첫 부분에 넣는다.
*/

// Last in : 선입 구조
// free_listp : 뒷 블록의 bp
// bp : 현 블록의 bp
void putFreeBlock(void* bp){
    
    SUCC_FREEP(bp) = free_listp; // 뒷블록의 bp값 = free_listp
    PREC_FREEP(bp) = NULL;       // 앞블록의 bp값 = NULL(앞블록은 선입 구조이기 때문에 없음)
    PREC_FREEP(free_listp) = bp; // 뒷블록 기준-> 앞블록(현블록)의 bp값 = bp
    free_listp = bp;             // free_listp는 다음에 들어올 것을 염두에 두고 bp로 갱신
}

/*
    removeBlock(bp) : 할당되거나 연결되는 가용 블록을 free list에서 없앤다.
*/

void removeBlock(void *bp){

    //free list의 첫번째 블록을 없앨 때
    if (bp == free_listp){
        PREC_FREEP(SUCC_FREEP(bp)) = NULL;
        free_listp = SUCC_FREEP(bp);
    }
    // free list 안에서 없앨 때
    else{

        SUCC_FREEP(PREC_FREEP(bp)) = SUCC_FREEP(bp);
        PREC_FREEP(SUCC_FREEP(bp)) = PREC_FREEP(bp);
    }
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

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
// 조정할 블록 위치와 요청 사이즈를 인자로 받는다.
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr; // 크기를 조절하고 싶은 힙의 시작 포인터
    void *newptr;       // 크기 조절 뒤의 새 힙의 시작 포인터
    size_t copySize;    // 복사할 힙의 크기
    
    newptr = mm_malloc(size);
    if (newptr == NULL) // 요청 사이즈가 0보다 작거나 같으면 반환을 한다.
      return NULL;

    // copySize = 조절하고 싶은 힙의 크기
    copySize = GET_SIZE(HDRP(oldptr));  

    // 원래 메모리 크기보다 적은 크기를 realloc하면 크기에 맞는 메모리만 할당되고 나머지는 안된다.
    if (size < copySize)
      copySize = size;
    memcpy(newptr, oldptr, copySize); // newptr에 oldptr를 시작으로 copySize만큼의 메모리 값을 복사한다.
    mm_free(oldptr);    // 기존의 힙을 반환한다.
    return newptr;
}














