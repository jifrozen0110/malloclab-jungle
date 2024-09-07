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
    "2조",
    /* First member's full name */
    "문지언",
    /* First member's email address */
    "jifrozen0110",
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

//워드 크기
#define WSIZE 4
//더블 워드
#define DSIZE 8
// 초기 가용 블록과 힙확장을 위한 기본 크기 (2의 12승)
#define CHUNKSIZE (1<<12)

#define MAX(x,y) ((x) > (y)? (x):(y))

// 크기 size와 alloc 할당 비트를 통합해서 헤더와 풋터에 저장할 수 있는 값을 리턴
#define PACK(size,alloc) ((size) |(alloc))

// 인자 p가 참조하는 워드를 읽어서 리턴한다
#define GET(p) (*(unsigned int*)(p))
//p가 가리키는 워드에 val 을 저장한다.
#define PUT(p,val) (*(unsigned int *) (p)=(val))

// 0x7은 하위 비트 3개만 제거해서 블록 크기만 추출
#define GET_SIZE(p) (GET(p) & ~0x7)
// 0x1 하위 비트 1개만 남겨서 할당인지 가용인지 추출
#define GET_ALLOC(p) (GET(p) & 0x1)

// 블록 헤더 위치 계산
#define HDRP(bp) ((char *) (bp) - WSIZE)
// 풋터 위치를 계산 bp블록의 시작 위치 HDRP (블록+헤더+풋터) - DSIZE(풋터의 크기))
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

// 다음 블록의 포인터 반환
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) -WSIZE)))
// 이전 블록의 포인터 반환
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

static char* heap_listp;

static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void place(void *bp,size_t asize);

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    // mem_sbrk를 통해 힙에 추가적인 메모리 공간을 할당 (16바이트) 만약 실패하면 -1을 반환
    if((heap_listp=mem_sbrk(4*WSIZE))==(void *)-1){
        return -1;
    }

    PUT(heap_listp,0);// 패딩 역할(정렬 목적)
    PUT(heap_listp+(1*WSIZE),PACK(DSIZE,1)); // 프롤로그 헤더
    PUT(heap_listp+(2*WSIZE),PACK(DSIZE,1)); // 프롤로그 풋터
    PUT(heap_listp+(3*WSIZE),PACK(0,1)); // 에필로그 헤더(끝나는 지점을 알리는)
    heap_listp+=(2*WSIZE); // 프롤로그 블록 이후 가용 블록을 가리키도록 포인터 이동


    if(extend_heap(CHUNKSIZE/WSIZE) == NULL){
        return -1;
    }
    return 0;
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    // 조정된 블록 크기 실제로 할당된 블록의 크기
    size_t asize;
    // 힙이 부족할 경우 확장해야 할 크기
    size_t extendsize;
    char *bp;

    if (size==0){
        return NULL;
    }

    if (size<=DSIZE){
        // 최소 블록 크기 16바이트 할당
        asize=2*DSIZE;
    }else{
        // size+DSIZE는 사용자 요청 size에 헤더와 풋터를 더함
        // 더블 워드 정렬을 위해 (DSIZE-1)를 더해 9의 배수로 올림
        asize=DSIZE*((size+(DSIZE)+(DSIZE-1))/DSIZE);
    }

    // find_fiit으로 가용 블록을 찾고
    // 적절한 가용 블록이 있으면 place로 블록 할당
    if((bp=find_fit(asize))!=NULL){
        place(bp,asize);
        return bp;
    }

    // 가용 블록이 없으면
    // extendsize를 할당하려는 블록 크기(asize)
    // 기본 확장 크기(chunksize)중 더 큰 값으로 설정한다.
    extendsize=MAX(asize,CHUNKSIZE);

    // 힙 확장
    if((bp=extend_heap(extendsize/WSIZE))==NULL){
        return NULL;
    }

    // 확장된 블록에 대해 할당 완료
    place(bp,asize);
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp){
    // 헤더를 통해 블록 사이즈를 가져옴
    size_t size=GET_SIZE(HDRP(bp));

    // 헤더에 가용상태 0을 넣음
    PUT(HDRP(bp), PACK(size,0));
    // 풋터에 가용상태 0을 넣음
    PUT(FTRP(bp),PACK(size,0));
    // 해제한 블록을 인접한 가용 블록들과 병함
    coalesce(bp);
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

//------------------------------------------------------

// extend_heap은 1) 힙이 초기화될 때
// 2) mm_malloc이 적당한 맞춤 fit을 찾지 못했을때
static void *extend_heap(size_t words){
    char *bp;
    size_t size;

    // 워드가 홀수인 경우 word%2 가 참 -> 더블 워드 정렬을 위해 +1로 짝수 맞춰줌
    size=(words%2) ? (words+1)*WSIZE: words*WSIZE;
    // mem_sbrk를 통해 힙 메모리 영역 할당 요청
    if ((long) (bp=mem_sbrk(size))==-1){
        return NULL;
    }
    //헤더 설정 0 블록이 가용 상태임을 나타냄
    PUT(HDRP(bp), PACK(size,0));
    // 풋터 설정
    PUT(FTRP(bp),PACK(size,0));
    //에필로그 헤더를 설정한다. 1 할당된 상태 끝을 알리는
    PUT(HDRP(NEXT_BLKP(bp)),PACK(0,1));

    // 인접한 가용 블록과 통합을 위한 함수 호출
    // 주변 가용 블록과 병합하여 메모리 조각화를 줄이고 큰 가용 블록을 만듦
    return coalesce(bp);
}



static void * coalesce(void *bp){
    // 이전 블록이 할당되었는지 확인
    size_t prev_alloc=GET_ALLOC(FTRP(PREV_BLKP(bp)));
    // 다음 블록이 할당되었는지 확인
    size_t next_alloc=GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    // 전체 블록 사이즈
    size_t size=GET_SIZE(HDRP(bp));

    // 이전 블록이 할당되었는지 다음블록이 할당 되었는지 확인
    // 1 할당 1 할당
    if (prev_alloc && next_alloc){
        // 아무것도 안하고 현재 블록 유지
        return bp;
    }
    // 이전 블록은 할당, 다음 블록은 가용
    else if (prev_alloc&& !next_alloc){
        // 다음 블록 전체 사이즈를 size에 더해줌
        size+=GET_SIZE(HDRP(NEXT_BLKP(bp)));
        // 헤더와 풋터에 0(가용)
        PUT(HDRP(bp),PACK(size,0));
        PUT(FTRP(bp),PACK(size,0));
    }
    // 이전 블록은 가용, 다음 블록은 할당
    else if(!prev_alloc&&next_alloc){
        //이전 블록만큼 size 더해줌
        size+=GET_SIZE(HDRP(PREV_BLKP(bp)));
        //픗터 헤더에 가용
        PUT(FTRP(bp), PACK(size,0));
        PUT(HDRP(PREV_BLKP(bp)),PACK(size,0));
        //블록 포인터를 이전 블록으로 옮김
        bp=PREV_BLKP(bp);
    }
    else{
        // 아전 블록과 다음 블록의 사이즈를 더해줌
        size+=GET_SIZE(HDRP(PREV_BLKP(bp)))+
        GET_SIZE(FTRP(NEXT_BLKP(bp)));
        // 이전 블록에 0 집어넣음
        PUT(HDRP(PREV_BLKP(bp)),PACK(size,0));
        // 다음 블록에 0 집어넣음
        PUT(FTRP(NEXT_BLKP(bp)),PACK(size,0));
        // 이전블록으로 위치 변경
        bp=PREV_BLKP(bp);
    }
    return bp;
}
// 첫 번째 맞는 가용 블록
static void *find_fit(size_t asize){
    void *bp;
    // heap_listp 시작 부분부터 반복 시작
    // 힙 끝을 나타내는 에필로그 블록을 만날때까지 계속 탐색
    // 다음 블록으로 이동
    for (bp=heap_listp; GET_SIZE(HDRP(bp)) > 0; bp=NEXT_BLKP(bp)){
        // 현재 블록이 가용 상태인지 확인하고 아니면
        // 현재 블록에 할당 사이즈를 넣을 수 있는지 검사
        if (!GET_ALLOC(HDRP(bp)) && (asize<=GET_SIZE(HDRP(bp)))){
            return bp;
        }
    }
    return NULL;
}

//
static void place(void *bp,size_t asize){
    size_t csize=GET_SIZE(HDRP(bp));

    // 현재 사용 가능한 사이즈 - 할당해야하는 사이즈
    // 8바이트가 넘으면 블록을 나누어 할당
    if((csize-asize)>=(2*DSIZE)){
        //할당 사이즈만큼 할당 상태로 변경
        PUT(HDRP(bp),PACK(asize,1));
        PUT(FTRP(bp), PACK(asize,1));
        // 다음 블록으로 이동
        bp=NEXT_BLKP(bp);
        // 나머지 size만큼 가용 상태로 변경
        PUT(HDRP(bp), PACK(csize-asize,0));
        PUT(FTRP(bp), PACK(csize-asize,0));
    }else{
        // 현재 블록 사이즈만큼 할당
        PUT(HDRP(bp), PACK(csize,1));
        PUT(FTRP(bp), PACK(csize,1));
    }
}









