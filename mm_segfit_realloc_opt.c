#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

team_t team = {
    /* Team name */
    "team11",
    /* First member's full name */
    "shhwang",
    /* First member's email address */
    "shhwangofficial@gmail.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* 기본 상수 & 매크로 */
#define WSIZE 4              // word size
#define DSIZE 8              // double word size
#define CHUNKSIZE (1 << 12)  // 힙 확장을 위한 기본 크기 (= 초기 빈 블록의 크기)
#define SEGREGATED_SIZE (12) // segregated list의 class 개수
#define MAX(x, y) (x > y ? x : y)

/* 가용 리스트를 접근/순회하는 데 사용할 매크로 */
#define PACK(size, alloc) (size | alloc)                              // size와 할당 비트를 결합, header와 footer에 저장할 값
#define GET(p) (*(unsigned int *)(p))                                 // p가 참조하는 워드 반환 (포인터라서 직접 역참조 불가능 -> 타입 캐스팅)
#define PUT(p, val) (*(unsigned int *)(p) = (unsigned int)(val))      // p에 val 저장
#define GET_SIZE(p) (GET(p) & ~0x7)                                   // 사이즈 (~0x7: ...11111000, '&' 연산으로 뒤에 세자리 없어짐)
#define GET_ALLOC(p) (GET(p) & 0x1)                                   // 할당 상태
#define HDRP(bp) ((char *)(bp)-WSIZE)                                 // Header 포인터
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)          // Footer 포인터 (🚨Header의 정보를 참조해서 가져오기 때문에, Header의 정보를 변경했다면 변경된 위치의 Footer가 반환됨에 유의)
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE))) // 다음 블록의 포인터
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp)-DSIZE)))   // 이전 블록의 포인터

static char *heap_listp;                                // 클래스의 시작
#define GET_SUCC(bp) (*(void **)((char *)(bp) + WSIZE)) // 다음 가용 블록의 주소
#define GET_PRED(bp) (*(void **)(bp))                   // 이전 가용 블록의 주소
#define GET_ROOT(class) (*(void **)((char *)(heap_listp) + (WSIZE * class)))

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void splice_free_block(void *bp); // 가용 리스트에서 제거
static void add_free_block(void *bp);    // 가용 리스트에 추가
static int get_class(size_t size);

int mm_init(void)
{
    if ((heap_listp = mem_sbrk((SEGREGATED_SIZE + 4) * WSIZE)) == (void *)-1) 
        return -1;
    PUT(heap_listp, 0);                                                    
    PUT(heap_listp + (1 * WSIZE), PACK((SEGREGATED_SIZE + 2) * WSIZE, 1)); 
    for (int i = 0; i < SEGREGATED_SIZE; i++)
        PUT(heap_listp + ((2 + i) * WSIZE), NULL);
    PUT(heap_listp + ((SEGREGATED_SIZE + 2) * WSIZE), PACK((SEGREGATED_SIZE + 2) * WSIZE, 1));
    PUT(heap_listp + ((SEGREGATED_SIZE + 3) * WSIZE), PACK(0, 1));                            
    heap_listp += (2 * WSIZE);

    if (extend_heap(4) == NULL)   // 마법의 구문
        return -1;
    // if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
    //     return -1;
    return 0;
}

void *mm_malloc(size_t size)
{
    size_t asize;    
    char *bp;

    if (size == 0) 
        return NULL;

    if (size <= DSIZE)     
        asize = 2 * DSIZE; 
    else
        asize = DSIZE * ((size + DSIZE + DSIZE - 1) / DSIZE); 

    if ((bp = find_fit(asize)) != NULL) 
    {
        place(bp, asize); 
        return bp;        
    }

    
    if ((bp = extend_heap(asize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}


void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void * bp;
    void *newptr;
    size_t copySize; //oldsize of block
    size_t asize;  // size는 말록용, asize는 이미 있는 블록 조정용
    if (size == 0)
        return NULL;
    
    if (size <= DSIZE)
        asize = 2*DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);

    copySize = GET_SIZE(HDRP(oldptr));

    if (asize <= copySize){
        return oldptr;
    }
    else {
        if (GET_ALLOC(HDRP(NEXT_BLKP(oldptr))) == 0 && (GET_SIZE(HDRP(NEXT_BLKP(oldptr))) + copySize) >= asize) {
                splice_free_block((NEXT_BLKP(oldptr)));
                size = GET_SIZE(HDRP(NEXT_BLKP(oldptr))) + copySize;
                PUT(HDRP(oldptr), PACK(size, 1));
                PUT(FTRP(oldptr), PACK(size, 1));


                // /* 분할 하는 코드 */
                // if ((size - asize) >= (2 * DSIZE)) 
                // {
                //     PUT(HDRP(oldptr), PACK(asize, 1)); 
                //     PUT(FTRP(oldptr), PACK(asize, 1));
                //     bp = NEXT_BLKP(oldptr); 
                //     PUT(HDRP(bp), PACK((size - asize), 0)); 
                //     PUT(FTRP(bp), PACK((size - asize), 0));
                //     add_free_block(bp); 
                // }
                // else
                // {
                //     PUT(HDRP(oldptr), PACK(size, 1)); 
                //     PUT(FTRP(oldptr), PACK(size, 1));

                // }


                return oldptr;
            }
        
        else {
            newptr = mm_malloc(size);
            if (newptr == NULL)
                return NULL;
        
            memcpy(newptr, oldptr, copySize);
            mm_free(oldptr);
            return newptr;
        }
    }
}

static void *extend_heap(size_t words)
{
    char *bp;

    size_t size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE; 

    if ((long)(bp = mem_sbrk(size)) == -1) 
        return NULL;

    PUT(HDRP(bp), PACK(size, 0));         
    PUT(FTRP(bp), PACK(size, 0));         
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); 
    
    return coalesce(bp); 
}

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); 
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); 
    size_t size = GET_SIZE(HDRP(bp));                   

    if (prev_alloc && next_alloc) 
    {
        add_free_block(bp); 
        return bp;          
    }
    else if (prev_alloc && !next_alloc) 
    {
        splice_free_block(NEXT_BLKP(bp)); 
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0)); 
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if (!prev_alloc && next_alloc) 
    {
        splice_free_block(PREV_BLKP(bp)); 
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); 
        PUT(FTRP(bp), PACK(size, 0));            
        bp = PREV_BLKP(bp);                    
    }
    else 
    {
        splice_free_block(PREV_BLKP(bp)); 
        splice_free_block(NEXT_BLKP(bp)); 
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); 
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0)); 
        bp = PREV_BLKP(bp);                     
    }
    add_free_block(bp); 
    return bp;          
}

static void *find_fit(size_t asize)
{
    int class = get_class(asize);
    void *bp = GET_ROOT(class);
    while (class < SEGREGATED_SIZE) 
    {
        bp = GET_ROOT(class);
        while (bp != NULL)
        {
            if ((asize <= GET_SIZE(HDRP(bp)))) 
                return bp;
            bp = GET_SUCC(bp); 
        }
        class += 1;
    }
    return NULL;
}

static void place(void *bp, size_t asize)
{
    splice_free_block(bp); 

    size_t csize = GET_SIZE(HDRP(bp)); 

    if ((csize - asize) >= (2 * DSIZE)) 
    {
        PUT(HDRP(bp), PACK(asize, 1)); 
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp); 

        PUT(HDRP(bp), PACK((csize - asize), 0)); 
        PUT(FTRP(bp), PACK((csize - asize), 0));
        add_free_block(bp); 
    }
    else
    {
        PUT(HDRP(bp), PACK(csize, 1)); 
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

static void splice_free_block(void *bp)
{
    int class = get_class(GET_SIZE(HDRP(bp)));
    if (bp == GET_ROOT(class)) 
    {
        GET_ROOT(class) = GET_SUCC(bp); 
        return;
    }

    GET_SUCC(GET_PRED(bp)) = GET_SUCC(bp);

    if (GET_SUCC(bp) != NULL) 
        GET_PRED(GET_SUCC(bp)) = GET_PRED(bp);
}


static void add_free_block(void *bp)
{
    int class = get_class(GET_SIZE(HDRP(bp)));
    GET_SUCC(bp) = GET_ROOT(class);     
    if (GET_ROOT(class) != NULL)       
        GET_PRED(GET_ROOT(class)) = bp; 
    GET_ROOT(class) = bp;
}

int get_class(size_t size)
{
    if (size < 16) 
        return -1; 

    size_t class_sizes[SEGREGATED_SIZE];
    class_sizes[0] = 16;


    for (int i = 0; i < SEGREGATED_SIZE; i++)
    {
        if (i != 0)
            class_sizes[i] = class_sizes[i - 1] << 1;
        if (size <= class_sizes[i])
            return i;
    }

    return SEGREGATED_SIZE - 1;
}