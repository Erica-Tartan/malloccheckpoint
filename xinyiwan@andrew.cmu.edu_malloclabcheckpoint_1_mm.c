/**
 * @file mm.c
 * @brief A 64-bit struct-based implicit free list memory allocator
 *
 * 15-213: Introduction to Computer Systems
 *
 *
 *************************************************************************
 *
 * ADVICE FOR STUDENTS.
 * - Step 0: Please read the writeup!
 * - Step 1: Write your heap checker.
 * - Step 2: Write contracts / debugging assert statements.
 * - Good luck, and have fun!
 *
 *************************************************************************
 *
 * @author Erica Wang <xinyiwan@andrew.cmu.edu>
 */

#include <assert.h>
#include <inttypes.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "memlib.h"
#include "mm.h"

/* Do not change the following! */

#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#define memset mem_memset
#define memcpy mem_memcpy
#endif /* def DRIVER */

/*
 *****************************************************************************
 * If DEBUG is defined (such as when running mdriver-dbg), these macros      *
 * are enabled. You can use them to print debugging output and to check      *
 * contracts only in debug mode.                                             *
 *                                                                           *
 * Only debugging macros with names beginning "dbg_" are allowed.            *
 * You may not define any other macros having arguments.                     *
 *****************************************************************************
 */
#ifdef DEBUG
/* When DEBUG is defined, these form aliases to useful functions */
#define dbg_printf(...) ((void)printf(__VA_ARGS__))
#define dbg_requires(expr) assert(expr)
#define dbg_assert(expr) assert(expr)
#define dbg_ensures(expr) assert(expr)
#define dbg_printheap(...) print_heap(__VA_ARGS__)
#else
/* When DEBUG is not defined, no code gets generated for these */
/* The sizeof() hack is used to avoid "unused variable" warnings */
#define dbg_printf(...) ((void)sizeof(__VA_ARGS__))
#define dbg_requires(expr) ((void)sizeof(expr))
#define dbg_assert(expr) ((void)sizeof(expr))
#define dbg_ensures(expr) ((void)sizeof(expr))
#define dbg_printheap(...) ((void)sizeof(__VA_ARGS__))
#endif

/* Basic constants */

typedef uint64_t word_t;

/** @brief Word and header size (bytes) */
static const size_t wsize = sizeof(word_t);

/** @brief Double word size (bytes) */
static const size_t dsize = 2 * wsize;

/** @brief Minimum block size (bytes) */
static const size_t min_block_size = 2 * dsize;

/**
 * size of heap increases by chunksize after each extension
 * (Must be divisible by dsize)
 */
static const size_t chunksize = (1 << 12);

/**
 * get the alloc (0 = free, 1 = allocated) info from header
 */
static const word_t alloc_mask = 0x1;

/**
 * get the previous block alloc (0 = free, 1 = allocated) info from header
 */

static const word_t prev_alloc_mask = 0x2;

/**
 * get the size from header
 */
static const word_t size_mask = ~(word_t)0xF;

/** @brief Represents the header and payload of one block in the heap */
typedef struct block {
    /** @brief Header contains size + allocation flag */
    word_t header;
    union {
        struct {
            struct block *next;
            struct block *prev;
        }; // doubly linked list
        char payload[0];
    };
} block_t;

/* Global variables */

/** @brief Pointer to first block in the heap */
static block_t *heap_start = NULL;

/*
 *****************************************************************************
 * The functions below are short wrapper functions to perform                *
 * bit manipulation, pointer arithmetic, and other helper operations.        *
 *                                                                           *
 * We've given you the function header comments for the functions below      *
 * to help you understand how this baseline code works.                      *
 *                                                                           *
 * Note that these function header comments are short since the functions    *
 * they are describing are short as well; you will need to provide           *
 * adequate details for the functions that you write yourself!               *
 *****************************************************************************
 */

/*
 * ---------------------------------------------------------------------------
 *                        BEGIN SHORT HELPER FUNCTIONS
 * ---------------------------------------------------------------------------
 */

/**
 * @brief Returns the maximum of two integers.
 * @param[in] x
 * @param[in] y
 * @return `x` if `x > y`, and `y` otherwise.
 */
static size_t max(size_t x, size_t y) {
    return (x > y) ? x : y;
}

/**
 * @brief Rounds `size` up to next multiple of n
 * @param[in] size
 * @param[in] n
 * @return The size after rounding up
 */
static size_t round_up(size_t size, size_t n) {
    size_t asize = n * ((size + (n - 1)) / n);
    if (asize < min_block_size) {
        return min_block_size;
    } else {
        return asize;
    }
}

/**
 * @brief Packs the `size` and `alloc` of a block into a word suitable for
 *        use as a packed value.
 *
 * Packed values are used for both headers and footers.
 *
 * The allocation status is packed into the lowest bit of the word.
 *
 * @param[in] size The size of the block being represented
 * @param[in] alloc True if the block is allocated
 * @return The packed value
 */
static word_t pack(size_t size, bool alloc, bool prev_alloc) {
    word_t word = size;
    if (alloc) {
        if (prev_alloc) {
            word = word | prev_alloc_mask | alloc_mask;
        } else {
            word = word | alloc_mask;
        }
    } else {
        if (prev_alloc) {
            word = word | prev_alloc_mask;
        }
    }
    return word;
}

/**
 * @brief Extracts the size represented in a packed word.
 *
 * This function simply clears the lowest 4 bits of the word, as the heap
 * is 16-byte aligned.
 *
 * @param[in] word
 * @return The size of the block represented by the word
 */
static size_t extract_size(word_t word) {
    return (word & size_mask);
}

/**
 * @brief Extracts the size of a block from its header.
 * @param[in] block
 * @return The size of the block
 */
static size_t get_size(block_t *block) {
    return extract_size(block->header);
}

/**
 * @brief Given a payload pointer, returns a pointer to the corresponding
 *        block.
 * @param[in] bp A pointer to a block's payload
 * @return The corresponding block
 */
static block_t *payload_to_header(void *bp) {
    return (block_t *)((char *)bp - offsetof(block_t, payload));
}

/**
 * @brief Given a block pointer, returns a pointer to the corresponding
 *        payload.
 * @param[in] block
 * @return A pointer to the block's payload
 * @pre The block must be a valid block, not a boundary tag.
 */
static void *header_to_payload(block_t *block) {
    dbg_requires(get_size(block) != 0);
    return (void *)(block->payload);
}

/**
 * @brief Given a block pointer, returns a pointer to the corresponding
 *        footer.
 * @param[in] block
 * @return A pointer to the block's footer
 * @pre The block must be a valid block, not a boundary tag.
 */
static word_t *header_to_footer(block_t *block) {
    dbg_requires(get_size(block) != 0 &&
                 "Called header_to_footer on the epilogue block");
    return (word_t *)(block->payload + get_size(block) - dsize);
}

/**
 * @brief Given a block footer, returns a pointer to the corresponding
 *        header.
 * @param[in] footer A pointer to the block's footer
 * @return A pointer to the start of the block
 * @pre The footer must be the footer of a valid block, not a boundary tag.
 */
static block_t *footer_to_header(word_t *footer) {
    size_t size = extract_size(*footer);
    dbg_assert(size != 0 && "Called footer_to_header on the prologue block");
    return (block_t *)((char *)footer + wsize - size);
}

/**
 * @brief Returns the payload size of a given block.
 *
 * The payload size is equal to the entire block size minus the sizes of the
 * block's header.
 *
 * @param[in] block
 * @return The size of the block's payload
 */
static size_t get_payload_size(block_t *block) {
    size_t asize = get_size(block);
    return asize - wsize;
}

/**
 * @brief Returns the allocation status of a given header value.
 *
 * This is based on the lowest bit of the header value.
 *
 * @param[in] word
 * @return The allocation status correpsonding to the word
 */
static bool extract_alloc(word_t word) {
    return (bool)(word & alloc_mask);
}

/**
 * @brief Returns the allocation status of a block, based on its header.
 * @param[in] block
 * @return The allocation status of the block
 */
static bool get_alloc(block_t *block) {
    return extract_alloc(block->header);
}

/**
 * Returns the allocation status of a given header value.
 * This is based on the second lowest bit of the header value.
 */

static bool extract_prev_alloc(word_t word) {
    return (bool)(word & prev_alloc_mask);
}

/**
 * Returns the allocation status of a block, based on its header.
 */
static bool get_prev_alloc(block_t *block) {
    return extract_prev_alloc(block->header);
}

/**
 * @brief Writes an epilogue header at the given address.
 *
 * The epilogue header has size 0, is marked as allocated,
 * and its prev block is not allocated (dummy).
 *
 * @param[out] block The location to write the epilogue header
 */
static void write_epilogue(block_t *block) {
    dbg_requires(block != NULL);
    dbg_requires((char *)block == (char *)mem_heap_hi() - 7);
    block->header = pack(0, true, false);
}

/**
 * @brief Writes a block starting at the given address.
 *
 * This function writes both a header and footer, where the location of the
 * footer is computed in relation to the header.
 *
 *
 * @param[out] block The location to begin writing the block header
 * @param[in] size The size of the new block
 * @param[in] alloc The allocation status of the new block
 */
static void write_block(block_t *block, size_t size, bool alloc,
                        bool prev_alloc) {
    dbg_requires(block != NULL);
    dbg_requires(size > 0);
    word_t word = pack(size, alloc, prev_alloc);
    block->header = word;
    // if the block is empty, we need to write the footer
    if (!alloc) {
        word_t *footerp = header_to_footer(block);
        *footerp = word;
    }
}

/**
 * @brief Finds the next consecutive block on the heap.
 *
 * This function accesses the next block in the "implicit list" of the heap
 * by adding the size of the block.
 *
 * @param[in] block A block in the heap
 * @return The next consecutive block on the heap
 * @pre The block is not the epilogue
 */
static block_t *find_next(block_t *block) {
    dbg_requires(block != NULL);
    dbg_requires(get_size(block) != 0 &&
                 "Called find_next on the last block in the heap");
    return (block_t *)((char *)block + get_size(block));
}

/**
 * update the prev alloc info (in the header) of the next block
 */
static void update_next_prev_alloc(block_t *block, bool next_prev_alloc) {
    dbg_requires(block != NULL);
    block_t *next_block = find_next(block);
    dbg_requires(next_block != NULL);
    word_t word =
        pack(get_size(next_block), get_alloc(next_block), next_prev_alloc);
    next_block->header = word;
}

/**
 * @brief Finds the footer of the previous block on the heap.
 * @param[in] block A block in the heap
 * @return The location of the previous block's footer
 */
static word_t *find_prev_footer(block_t *block) {
    // Compute previous footer position as one word before the header
    return &(block->header) - 1;
}

/**
 * @brief Finds the previous consecutive block on the heap.
 *
 * This is the previous block in the "implicit list" of the heap.
 *
 * If the function is called on the first block in the heap, NULL will be
 * returned, since the first block in the heap has no previous block!
 *
 * The position of the previous block is found by reading the previous
 * block's footer to determine its size, then calculating the start of the
 * previous block based on its size.
 *
 * @param[in] block A block in the heap
 * @return The previous consecutive block in the heap.
 */
static block_t *find_prev(block_t *block) {
    dbg_requires(block != NULL);
    word_t *footerp = find_prev_footer(block);

    // Return NULL if called on first block in the heap
    if (extract_size(*footerp) == 0) {
        return NULL;
    }

    return footer_to_header(footerp);
}

/*
 * ---------------------------------------------------------------------------
 *                        END SHORT HELPER FUNCTIONS
 * ---------------------------------------------------------------------------
 */

/******** The remaining content below are helper and debug routines ********/
static const int list_length =
    15;                       // There are 15 block lists in my segregated list
static block_t *seg_list[15]; // doubly linked list implementation

static const word_t list0 = 32;     //[32,64)
static const word_t list1 = 64;     //[64,96)
static const word_t list2 = 96;     //[96,128)
static const word_t list3 = 128;    //[128,192)
static const word_t list4 = 160;    //[128,192)
static const word_t list5 = 192;    //[192,256)
static const word_t list6 = 256;    //[256,512)
static const word_t list7 = 512;    //[512,1024)
static const word_t list8 = 1024;   //[1024,2048)
static const word_t list9 = 2048;   //[2048,4096)
static const word_t list10 = 4096;  //[4096,8192)
static const word_t list11 = 8192;  //[8192,16384)
static const word_t list12 = 16384; //[16384,32768)
static const word_t list13 = 32768; //[32768,65536)
static const word_t list14 = 65536; //[65536,inf)

// declare ahead to be called
static void print_linkedList(void);
static block_t *coalesce_block(block_t *block);

/**
 * find the index of the block in seg_list
 */
static int find_index(size_t size) {
    int list_index;
    if (size >= list0 && size < list1) {
        list_index = 0;
    } else if (size >= list1 && size < list2) {
        list_index = 1;
    } else if (size >= list2 && size < list3) {
        list_index = 2;
    } else if (size >= list3 && size < list4) {
        list_index = 3;
    } else if (size >= list4 && size < list5) {
        list_index = 4;
    } else if (size >= list5 && size < list6) {
        list_index = 5;
    } else if (size >= list6 && size < list7) {
        list_index = 6;
    } else if (size >= list7 && size < list8) {
        list_index = 7;
    } else if (size >= list8 && size < list9) {
        list_index = 8;
    } else if (size >= list9 && size < list10) {
        list_index = 9;
    } else if (size >= list10 && size < list11) {
        list_index = 10;
    } else if (size >= list11 && size < list12) {
        list_index = 11;
    } else if (size >= list12 && size < list13) {
        list_index = 12;
    } else if (size >= list13 && size < list14) {
        list_index = 13;
    } else {
        list_index = 14;
    }
    return list_index;
}

/**
 * remove the block (should be free) from seg_list
 */
static void remove_from_list(block_t *block) {
    size_t size = get_size(block);
    int index = find_index(size);
    block_t *block_prev = block->prev;
    block_t *block_next = block->next;
    if (block_prev == NULL && block_next == NULL) {
        seg_list[index] = NULL;
    } else if (block_prev != NULL &&
               block_next == NULL) { /* currently at the last free block*/
        block_prev->next = NULL;
    } else if (block_prev == NULL &&
               block_next != NULL) { /* currently at the first free block*/
        seg_list[index] = block_next;
        block_next->prev = NULL;
    } else { /* neither block_prev nor block_next is NULL */
        block_prev->next = block_next;
        block_next->prev = block_prev;
    }
}

/**
 * add the block (should be free) to seg_list
 */
static void add_to_list(block_t *block) { /* FIFO insertion */
    size_t size = get_size(block);
    int index = find_index(size);
    if (seg_list[index] ==
        NULL) { /* block is the only elem in seg_list[index] */
        block->next = NULL;
        block->prev = NULL;
        seg_list[index] = block;
    } else {
        block->prev = NULL;
        block->next = seg_list[index];
        seg_list[index]->prev = block;
        seg_list[index] = block;
    }
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] size
 * @return
 */
static block_t *extend_heap(size_t size) {
    void *bp;

    // Allocate an even number of words to maintain alignment
    size = round_up(size, dsize);
    if ((bp = mem_sbrk((intptr_t)size)) == (void *)-1) {
        return NULL;
    }

    // Initialize free block header/footer
    block_t *block = payload_to_header(bp);
    write_block(block, size, false, get_prev_alloc(block));

    // Create new epilogue header
    block_t *block_next = find_next(block);
    write_epilogue(block_next);

    // Coalesce in case the previous block was free
    block = coalesce_block(block);
    add_to_list(block);

    // printf("printing linkedList in extend heap\n...");
    // print_linkedList();

    dbg_requires(mm_checkheap(__LINE__));
    return block;
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] block
 * @param[in] asize
 */
static void split_block(block_t *block, size_t asize) {
    dbg_requires(asize % dsize == 0);
    /* TODO: Can you write a precondition about the value of asize? */
    remove_from_list(block);
    size_t block_size = get_size(block);

    if ((block_size - asize) >= min_block_size) {
        block_t *block_next;
        write_block(block, asize, true, get_prev_alloc(block));

        block_next = find_next(block);
        write_block(block_next, block_size - asize, false, true);
        add_to_list(block_next);
    } else {
        write_block(block, block_size, true, get_prev_alloc(block));
        update_next_prev_alloc(block, true);
    }

    dbg_ensures(get_alloc(block));
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] asize
 * @return
 */
static block_t *find_fit(size_t asize) {
    block_t *block;
    int index;
    for (index = find_index(asize); index < list_length; index++) {
        block = seg_list[index];
        while (block != NULL) {
            if (!(get_alloc(block)) && (asize <= get_size(block))) {
                return block;
            }
            block = block->next;
        }
    }
    return NULL;
}

/*
 * ---------------------------------------------------------------------------
 *                        BEGIN DEBUG HELPER FUNCTIONS
 * ---------------------------------------------------------------------------
 */

static void print_linkedList() {
    block_t *block;
    int index;
    for (index = 0; index < list_length; index++) {
        printf("seg_list index = %d\n", index);
        for (block = seg_list[index]; block != NULL; block = block->next) {
            printf("alloc = %d\n", get_alloc(block));
            printf("prev_alloc = %d\n", get_prev_alloc(block));
            printf("size = %ld\n", get_size(block));
        }
    }
}

static void print_heap() {
    block_t *block;
    for (block = heap_start; get_size(block) > 0; block = find_next(block)) {
        printf("alloc = %d\n", get_alloc(block));
        printf("prev_alloc = %d\n", get_prev_alloc(block));
        printf("size = %ld\n", get_size(block));
    }
}

/********       The functions below are called in mm_checkheap      ********/
static bool check_payload_align() {
    block_t *block;
    for (block = heap_start; get_size(block) > 0; block = find_next(block)) {
        if (get_alloc(block)) {
            intptr_t payload_addr = (intptr_t)header_to_payload(block);
            if (payload_addr % 16 != 0) {
                return false;
            }
        }
    }
    return true;
}

static bool check_acyclic(block_t *free_list) {
    if (free_list == NULL) {
        return true;
    }
    block_t *turtle = free_list;
    block_t *rabbit = free_list->next;
    while (turtle != rabbit) {
        if (rabbit == NULL || rabbit->next == NULL) {
            return true;
        }
        turtle = turtle->next;
        rabbit = rabbit->next;
        rabbit = rabbit->next;
    }
    return false;
}

static bool check_no_block_loss() {
    int index;
    size_t length = 0;
    block_t *block1;
    for (index = 0; index < list_length; index++) {
        for (block1 = seg_list[index]; block1 != NULL; block1 = block1->next) {
            length++;
        }
    }

    block_t *block2;
    size_t res = 0;
    for (block2 = heap_start; get_size(block2) > 0;
         block2 = find_next(block2)) {
        if (!get_alloc(block2)) {
            res++;
        }
    }

    // Check if these two counting matches
    if (length == res) {
        return true;
    } else {
        printf("Sum all free lists: %zu\n", length);
        printf("Count by traversing heap: %zu\n", res);
        return false;
    }
}

static bool check_no_consecutive_free_blocks() {
    block_t *block;
    for (block = heap_start; get_size(block) > 0; block = find_next(block)) {
        block_t *next = find_next(block);
        // if "next" is not the epilogue
        if (get_size(next) > 0) {
            bool is_cur_free = !get_alloc(block);
            bool is_next_free = !get_alloc(next);
            if (is_cur_free && is_next_free)
                return false;
        }
    }
    return true;
}

static bool check_epi_prologue() {
    block_t *epilogue = (block_t *)((char *)mem_heap_hi() - 7);
    bool epi = (get_alloc(epilogue)) && (get_size(epilogue) == 0);
    block_t *prologue = (block_t *)((char *)mem_heap_lo());
    bool pro = (get_alloc(prologue)) && (get_size(prologue) == 0);
    return epi && pro;
}

static bool check_range() {
    block_t *block;
    for (block = heap_start; get_size(block) > 0; block = find_next(block)) {
        if (((intptr_t)block <= (intptr_t)(mem_heap_lo())) ||
            ((intptr_t)block >= (intptr_t)(mem_heap_hi()) - 7)) {
            return false;
        }
    }
    return true;
}

static bool check_free_list_consistent() {
    block_t *block;
    int index;
    for (index = 0; index < list_length; index++) {
        for (block = seg_list[index]; block != NULL; block = block->next) {
            if (block->next != NULL) {
                if (block->next->prev != block) {
                    return false;
                }
            }
        }
    }
    return true;
}

static bool check_free_list_size_range() {
    block_t *block;
    int index;
    size_t lo;
    size_t hi;
    for (index = 0; index < list_length; index++) {
        if (index == 0) {
            lo = list0;
            hi = list1;
        } else if (index == 1) {
            lo = list1;
            hi = list2;
        } else if (index == 2) {
            lo = list2;
            hi = list3;
        } else if (index == 3) {
            lo = list3;
            hi = list4;
        } else if (index == 4) {
            lo = list4;
            hi = list5;
        } else if (index == 5) {
            lo = list5;
            hi = list6;
        } else if (index == 6) {
            lo = list6;
            hi = list7;
        } else if (index == 7) {
            lo = list7;
            hi = list8;
        } else if (index == 8) {
            lo = list8;
            hi = list9;
        } else if (index == 9) {
            lo = list9;
            hi = list10;
        } else if (index == 10) {
            lo = list10;
            hi = list11;
        } else if (index == 11) {
            lo = list11;
            hi = list12;
        } else if (index == 12) {
            lo = list12;
            hi = list13;
        } else if (index == 13) {
            lo = list13;
            hi = list14;
        } else {
            lo = list14;
            hi = 0xffffffffffffffff;
        }
        for (block = seg_list[index]; block != NULL; block = block->next) {
            size_t size = get_size(block);
            if (size < lo || size >= hi) {
                return false;
            }
        }
    }
    return true;
}

static bool check_free_list_pointer_range() {
    block_t *block;
    int index;
    for (index = 0; index < list_length; index++) {
        for (block = seg_list[index]; block != NULL; block = block->next) {
            if (block->prev != NULL) {
                if (((intptr_t)block->prev <= (intptr_t)(mem_heap_lo())) ||
                    ((intptr_t)block->prev >= (intptr_t)(mem_heap_hi()) - 7)) {
                    return false;
                }
            }
            if (block->next != NULL) {
                if (((intptr_t)block->next <= (intptr_t)(mem_heap_lo())) ||
                    ((intptr_t)block->next >= (intptr_t)(mem_heap_hi()) - 7)) {
                    return false;
                }
            }
        }
    }
    return true;
}

static bool check_curr_next_consistency() {
    block_t *block;
    for (block = heap_start; get_size(block) > 0; block = find_next(block)) {
        block_t *next = find_next(block);
        // if "next" is not the epilogue
        if (get_size(next) > 0) {
            if (get_prev_alloc(next) != get_alloc(block)) {
                return false;
            }
        }
    }
    return true;
}

static bool check_header_footer_consistency() {
    block_t *block;
    for (block = heap_start; get_size(block) > 0; block = find_next(block)) {
        if (!get_alloc(block)) {
            word_t *ptr_to_header = &block->header;
            word_t *ptr_to_footer = header_to_footer(block);
            // compare
            if (*ptr_to_header != *ptr_to_footer) {
                return false;
            }
        }
    }
    return true;
}
/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] line
 * @return
 */
bool mm_checkheap(int line) {
    bool errorflag = true;
    if (!check_payload_align()) {
        printf("payload not aligned\n");
        errorflag = false;
    }

    int index;
    for (index = 0; index < list_length; index++) {
        if (!check_acyclic(seg_list[index])) {
            printf("free list cyclic\n");
            errorflag = false;
        }
    }

    if (!check_epi_prologue()) {
        printf("bad epilogue or prologue blocks\n");
        errorflag = false;
    }

    if (!check_range()) {
        printf("block address out of range\n");
        errorflag = false;
    }

    if (!check_free_list_consistent()) {
        printf("block->next->prev != block\n");
        errorflag = false;
    }

    if (!check_free_list_size_range()) {
        printf("block size is out of the size range of the block list it "
               "belongs to\n");
        errorflag = false;
    }

    if (!check_free_list_pointer_range()) {
        printf("block->prev / block->next address out of range\n");
        errorflag = false;
    }

    if (!check_header_footer_consistency()) {
        printf(
            "for some free blocks, the header and footer are inconsistent\n");
        errorflag = false;
    }

    if (!check_curr_next_consistency()) {
        printf("the alloc info of some block is inconsistent with the prev "
               "alloc info of its following block\n");
        errorflag = false;
    }

    if (!check_no_consecutive_free_blocks()) {
        printf("exist consecutive free blocks\n");
        errorflag = false;
    }

    if (!check_no_block_loss()) {
        printf("block loss\n");
        errorflag = false;
    }

    // print_heap();
    // print_linkedList();
    return errorflag;
}

/*
 * ---------------------------------------------------------------------------
 *                        END DEBUG HELPER FUNCTIONS
 * ---------------------------------------------------------------------------
 */

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @return
 */
bool mm_init(void) {
    // Create the initial empty heap
    word_t *start = (word_t *)(mem_sbrk(2 * wsize));

    if (start == (void *)-1) {
        return false;
    }

    start[0] = pack(0, true, true); // Heap prologue (block footer)
    start[1] = pack(0, true, true); // Heap epilogue (block header)

    // Heap starts with first "block header", currently the epilogue
    heap_start = (block_t *)&(start[1]);

    int index;
    for (index = 0; index < list_length; index++) {
        seg_list[index] = NULL;
    }

    // Extend the empty heap with a free block of chunksize bytes
    if (extend_heap(chunksize) == NULL) {
        return false;
    }
    return true;
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] size
 * @return
 */
void *malloc(size_t size) {
    size_t asize;      // Adjusted block size
    size_t extendsize; // Amount to extend heap if no fit is found
    block_t *block;
    void *bp = NULL;

    // Initialize heap if it isn't initialized
    if (heap_start == NULL) {
        mm_init();
    }

    // Ignore spurious request
    if (size == 0) {
        dbg_ensures(mm_checkheap(__LINE__));
        return bp;
    }

    // Adjust block size to include overhead and to meet alignment requirements
    asize = round_up(size + wsize, dsize);

    // Search the free list for a fit
    block = find_fit(asize);

    // If no fit is found, request more memory, and then and place the block
    if (block == NULL) {
        // Always request at least chunksize
        extendsize = max(asize, chunksize);
        block = extend_heap(extendsize);
        // extend_heap returns an error
        if (block == NULL) {
            return bp;
        }
    }

    // The block should be marked as free
    dbg_assert(!get_alloc(block));

    // Try to split the block if too large
    split_block(block, asize);

    bp = header_to_payload(block);

    dbg_ensures(mm_checkheap(__LINE__));
    // printf("printing heap in malloc... \n");
    // print_heap();
    return bp;
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] bp
 */
void free(void *bp) {
    if (bp == NULL) {
        return;
    }

    block_t *block = payload_to_header(bp);
    size_t size = get_size(block);

    // The block should be marked as allocated
    dbg_assert(get_alloc(block));

    // Mark the block as free
    // printf("start writing \n");
    write_block(block, size, false, get_prev_alloc(block));
    // printf("writing successful\n");
    update_next_prev_alloc(block, false);
    // printf("update_next_prev_alloc successful\n");

    // Try to coalesce the block with its neighbors
    block = coalesce_block(block);
    add_to_list(block);
    // printf("printing linkedList in free\n...");
    // print_linkedList();
    // printf("coalesce successful\n");
    dbg_ensures(mm_checkheap(__LINE__));
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] ptr
 * @param[in] size
 * @return
 */
void *realloc(void *ptr, size_t size) {
    block_t *block = payload_to_header(ptr);
    size_t copysize;
    void *newptr;

    // If size == 0, then free block and return NULL
    if (size == 0) {
        free(ptr);
        return NULL;
    }

    // If ptr is NULL, then equivalent to malloc
    if (ptr == NULL) {
        return malloc(size);
    }

    // Otherwise, proceed with reallocation
    newptr = malloc(size);

    // If malloc fails, the original block is left untouched
    if (newptr == NULL) {
        return NULL;
    }

    // Copy the old data
    copysize = get_payload_size(block); // gets size of old payload
    if (size < copysize) {
        copysize = size;
    }
    memcpy(newptr, ptr, copysize);

    // Free the old block
    free(ptr);

    return newptr;
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] elements
 * @param[in] size
 * @return
 */
void *calloc(size_t elements, size_t size) {
    void *bp;
    size_t asize = elements * size;

    if (elements == 0) {
        return NULL;
    }
    if (asize / elements != size) {
        // Multiplication overflowed
        return NULL;
    }

    bp = malloc(asize);
    if (bp == NULL) {
        return NULL;
    }

    // Initialize all bits to 0
    memset(bp, 0, asize);

    return bp;
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] block
 * @return
 */
static block_t *coalesce_block(block_t *block) {
    bool prev_alloc;

    block_t *prev = find_prev(block);
    if (block != NULL) {
        if (prev == NULL) { /* prev block is dummy */
            prev_alloc = true;
        } else {
            // printf("size = %lx\n", get_size(prev));
            prev_alloc = get_prev_alloc(block);
        }
        bool next_alloc = get_alloc(find_next(block));
        size_t size = get_size(block);
        // printf("curr size = %ld\n", size);
        if (prev_alloc && next_alloc) { /* Case 1 */
            // printf("entering case 1\n...");
            // printf("printing heap in coalesce\n...");
            // print_heap();
            // printf("printing linkedList in coalesce\n...");
            // print_linkedList();

            update_next_prev_alloc(block, false);
            return block;
        } else if (prev_alloc && !next_alloc) { /* Case 2 */
            // printf("entering case 2\n...");
            size += get_size(find_next(block));
            // printf("480 size = %ld\n", size);
            // write header and footer
            remove_from_list(find_next(block));
            write_block(block, size, false, true);
        } else if (!prev_alloc && next_alloc) { /* Case 3 */
            // printf("entering case 3\n...");
            size += get_size(prev);
            // printf("485 size = %ld\n", size);
            remove_from_list(prev);
            write_block(prev, size, false, get_prev_alloc(prev));
            block = prev;
        } else { /* Case 4, !prev_alloc && !next_alloc */
            // printf("entering case 4\n...");
            // printf("size = %lx\n", get_size(prev));
            size += get_size(prev) + get_size(find_next(block));
            // printf("492 size = %ld\n", size);
            remove_from_list(prev);
            remove_from_list(find_next(block));
            write_block(prev, size, false, get_prev_alloc(prev));
            block = prev;
        }
    }

    // printf("printing heap in coalesce\n...");
    // print_heap();
    // printf("printing linkedList in coalesce\n...");
    // print_linkedList();
    update_next_prev_alloc(block, false);
    return block;
}

/*
 *****************************************************************************
 * Do not delete the following super-secret(tm) lines!                       *
 *                                                                           *
 * 53 6f 20 79 6f 75 27 72 65 20 74 72 79 69 6e 67 20 74 6f 20               *
 *                                                                           *
 * 66 69 67 75 72 65 20 6f 75 74 20 77 68 61 74 20 74 68 65 20               *
 * 68 65 78 61 64 65 63 69 6d 61 6c 20 64 69 67 69 74 73 20 64               *
 * 6f 2e 2e 2e 20 68 61 68 61 68 61 21 20 41 53 43 49 49 20 69               *
 *                                                                           *
 * 73 6e 27 74 20 74 68 65 20 72 69 67 68 74 20 65 6e 63 6f 64               *
 * 69 6e 67 21 20 4e 69 63 65 20 74 72 79 2c 20 74 68 6f 75 67               *
 * 68 21 20 2d 44 72 2e 20 45 76 69 6c 0a c5 7c fc 80 6e 57 0a               *
 *                                                                           *
 *****************************************************************************
 */
