/**
 * @file mm.c
 * @brief A 64-bit struct-based implicit free list memory allocator
 *
 * 15-213: Introduction to Computer Systems
 *
 * Explicit List实现：
 *
 * Placement policy：first fit
 * Splitting policy：不少于最小块的大小即可
 * Coalescing policy：immediate coalesce
 * Insertion policy：LIFO
 * Eliminating Footers：none
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
 * @author Your Name <andrewid@andrew.cmu.edu>
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

/* You can change anything from here onward */

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
#define dbg_printf(...) printf(__VA_ARGS__)
#define dbg_requires(expr) assert(expr)
#define dbg_assert(expr) assert(expr)
#define dbg_ensures(expr) assert(expr)
#define dbg_printheap(...) print_heap(__VA_ARGS__)
#else
/* When DEBUG is not defined, no code gets generated for these */
/* The sizeof() hack is used to avoid "unused variable" warnings */
#define dbg_printf(...) (sizeof(__VA_ARGS__), -1)
#define dbg_requires(expr) (sizeof(expr), 1)
#define dbg_assert(expr) (sizeof(expr), 1)
#define dbg_ensures(expr) (sizeof(expr), 1)
#define dbg_printheap(...) ((void)sizeof(__VA_ARGS__))
#endif

/* Basic constants */

typedef uint64_t word_t;
typedef uint8_t byte_t;

/** @brief Word and header size (bytes) */
static const size_t wsize = sizeof(word_t);

/** @brief Double word size (bytes) */
static const size_t dsize = 2 * wsize;

/** @brief Minimum block size (bytes)
 *
 * header + prev pointer + next pointer + footer
 * 不允许Payload为0
 */
static const size_t min_block_size = 4 * wsize + dsize;

static const size_t overhead_size = 4 * wsize;

/**
 * sbrk一次移动的最小长度，现在是4KB
 * 需要在利用率和吞吐量之间平衡
 * (Must be divisible by dsize)
 */
static const size_t chunksize = (1 << 12);

/**
 * Header以及Footer的低位，用于表示当前Block是否被分配
 */
static const word_t alloc_mask = 0x1;

/**
 * @brief 由于地址是双字对齐的，因此低4位不会被用到
 *
 */
static const word_t low_order_mask = (word_t)0xF;

/**
 * 用于计算Block大小的掩码，单位是Byte
 */
static const word_t size_mask = ~(word_t)0xF;

/** @brief Represents the header and payload of one block in the heap */
typedef struct block {
  /** @brief Header contains size + allocation flag */
  word_t header;

  /** @brief 指向free list中前一个block的指针 */
  struct block *prev;

  /** @brief 指向free list中后一个block的指针 */
  struct block *next;

  /** @brief Same as header */
  word_t footer;

  /**
   * @brief A pointer to the block payload.
   *
   * We don't know what the size of the payload will be, so we will declare
   * it as a zero-length array, which is a GCC compiler extension. This will
   * allow us to obtain a pointer to the start of the payload.
   *
   * 可以通过block->payload获取payload的地址
   *
   * WARNING: A zero-length array must be the last element in a struct, so
   * there should not be any struct fields after it. For this lab, we will
   * allow you to include a zero-length array in a union, as long as the
   * union is the last field in its containing struct. However, this is
   * compiler-specific behavior and should be avoided in general.
   *
   * 零长度数组字段必须是结构体的最后一个字段，但是可以将这个字段包在一个Union里边
   * 只需确保Union也是结构体的最后一个字段即可
   *
   * WARNING: DO NOT cast this pointer to/from other types! Instead, you
   * should use a union to alias this zero-length array with another struct,
   * in order to store additional types of data in the payload memory.
   *
   * 不要使用强制类型转换将此字段变为其他类型，最好使用一个Union将其包裹起来
   * 不过Union中的其他成员可以是结构体，可以使用它们来保存一些其他的数据
   */
  char payload[0];

  /*
   * TODO: delete or replace this comment once you've thought about it.
   * Why can't we declare the block footer here as part of the struct?
   * Why do we even have footers -- will the code work fine without them?
   * which functions actually use the data contained in footers?
   */
} block_t;

/* Global variables */

/**
 * @brief Pointer to first block in the heap
 *
 * 实际是prologue的尾巴 */
static block_t *heap_start = NULL;

/**
 * @brief free list头节点
 * 不会是epilogue block
 */
static block_t *free_list_root = NULL;

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
 * adequate details within your header comments for the functions above!     *
 *****************************************************************************
 */

/*
 * ---------------------------------------------------------------------------
 *                        BEGIN SHORT HELPER FUNCTIONS
 * ---------------------------------------------------------------------------
 */

/* Declaration start */

static bool check_free_block_aux(block_t *);
static bool valid_block_format(block_t *);
static bool check_word_align_dword(word_t);

/* Declaration end */

/**
 * @brief Returns the maximum of two integers.
 * @param[in] x
 * @param[in] y
 * @return `x` if `x > y`, and `y` otherwise.
 */
static size_t max(size_t x, size_t y) { return (x > y) ? x : y; }

/**
 * @brief Rounds `size` up to next multiple of n
 * @param[in] size
 * @param[in] n
 * @return The size after rounding up
 */
static size_t round_up(size_t size, size_t n) {
  return n * ((size + (n - 1)) / n);
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
static word_t pack(size_t size, bool alloc) {
  word_t word = size;
  if (alloc) {
    word |= alloc_mask;
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
static size_t extract_size(word_t word) { return (word & size_mask); }

/**
 * @brief Extracts the size of a block from its header.
 * @param[in] block
 * @return The size of the block
 */
static size_t get_size(block_t *block) { return extract_size(block->header); }

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
 */
static void *header_to_payload(block_t *block) {
  return (void *)(block->payload);
}

/**
 * @brief Given a block pointer, returns a pointer to the corresponding
 *        footer.
 * @param[in] block
 * @return A pointer to the block's footer
 */
static word_t *header_to_footer(block_t *block) {
  return (word_t *)(block->payload + get_size(block) - 3 * wsize);
}

/**
 * @brief Given a block footer, returns a pointer to the corresponding
 *        header.
 * @param[in] footer A pointer to the block's footer
 * @return A pointer to the start of the block
 */
static block_t *footer_to_header(word_t *footer) {
  size_t size = extract_size(*footer);
  return (block_t *)((char *)footer + wsize - size);
}

/**
 * @brief Returns the payload size of a given block.
 *
 * The payload size is equal to the entire block size minus the sizes of the
 * block's header and footer.
 *
 * @param[in] block
 * @return The size of the block's payload
 */
static size_t get_payload_size(block_t *block) {
  size_t asize = get_size(block);
  return asize - overhead_size;
}

/**
 * @brief Returns the allocation status of a given header value.
 *
 * This is based on the lowest bit of the header value.
 *
 * @param[in] word
 * @return The allocation status correpsonding to the word
 */
static bool extract_alloc(word_t word) { return (bool)(word & alloc_mask); }

/**
 * @brief Returns the allocation status of a block, based on its header.
 * @param[in] block
 * @return The allocation status of the block
 */
static bool get_alloc(block_t *block) { return extract_alloc(block->header); }

/**
 * @brief Writes an epilogue header at the given address.
 *
 * The epilogue header has size 0, and is marked as allocated.
 *
 * @param[out] block The location to write the epilogue header
 * @pre block == mem_heap_hi() - 7
 */
static void write_epilogue(block_t *block) {
  dbg_requires(block != NULL);
  dbg_requires((char *)block == mem_heap_hi() - 7);

  block->header = pack(0, true);
}

/**
 * @brief Writes a block starting at the given address.
 * @pre size >= min_block_size
 * @pre size 对齐 16Byte
 *
 * This function writes both a header and footer, where the location of the
 * footer is computed in relation to the header.
 *
 * TODO: Are there any preconditions or postconditions?
 *
 * @param[out] block The location to begin writing the block header
 * @param[in] size The size of the new block
 * @param[in] alloc The allocation status of the new block
 */
static void write_block(block_t *block, size_t size, bool alloc) {
  dbg_requires(block != NULL);
  dbg_requires(size >= min_block_size);
  dbg_requires(check_word_align_dword((word_t)size));

  block->header = pack(size, alloc);
  word_t *footerp = header_to_footer(block);
  *footerp = pack(size, alloc);
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
  dbg_requires(get_size(block) != 0);
  return (block_t *)((char *)block + get_size(block));
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
 * The position of the previous block is found by reading the previous
 * block's footer to determine its size, then calculating the start of the
 * previous block based on its size.
 *
 * @param[in] block A block in the heap
 * @return The previous consecutive block in the heap
 * @pre The block is not the first block in the heap
 */
static block_t *find_prev(block_t *block) {
  dbg_requires(block != NULL);
  dbg_requires(get_size(block) != 0);

  word_t *footerp = find_prev_footer(block);
  return footer_to_header(footerp);
}

/**
 * @brief 将CURR插入到FRONT之后
 *
 * @note FRONT不可以是链表的最后一个元素
 *
 * @param front block_t，CURR会被插入到它之后
 * @param curr block_t，不可位于任何链表中
 * @pre FRONT和CURR都不可以是已分配的块
 * FRONT不可以是链表的最后一个元素
 */
static void insert_after(block_t *front, block_t *curr) {
  dbg_assert(front != NULL);
  dbg_assert(get_size(front) != 0);
  dbg_assert(get_alloc(front) == false);
  dbg_assert(check_free_block_aux(front) == true);
  dbg_assert(curr != NULL);
  dbg_assert(get_size(curr) != 0);
  dbg_assert(get_alloc(curr) == false);
  dbg_assert(valid_block_format(curr) == true);

  curr->next = front->next;
  curr->prev = front;
  front->next = curr;
  if(curr->next != NULL)
    curr->next->prev = curr;
}

/**
 * @brief 将CURR插入到BACK之前
 *
 * @note CURR不可以是链表的第一个元素
 *
 * @param curr 不可位于任何链表中
 * @param back CURR会被插入到它之前
 * @pre CURR和BACK都不可以是已分配的块
 * CURR不可以是链表的第一个元素
 */
static void insert_before(block_t *curr, block_t *back) {
  dbg_assert(back != NULL);
  dbg_assert(get_size(back) != 0);
  dbg_assert(get_alloc(back) == false);
  dbg_assert(check_free_block_aux(back) == true);
  dbg_assert(curr != NULL);
  dbg_assert(get_size(curr) != 0);
  dbg_assert(get_alloc(curr) == false);
  dbg_assert(valid_block_format(curr) == true);

  curr->prev = back->prev;
  curr->next = back;
  back->prev = curr;
  if(curr->prev != NULL)
    curr->prev->next = curr;
}

/**
 * @brief 将NEW_HEAD插入到ROOT所指向的链表的头部
 *
 * @param root 指向链表的第一个元素的指针
 * @param new_head 将要被插入到ROOT所指向的链表的元素
 * @pre NEW_HEAD不可以是已分配的块
 */
static void push_front(block_t **root, block_t *new_head) {
  dbg_assert(root != NULL);
  dbg_assert(&root != NULL);
  dbg_assert(check_free_block_aux(&root) == true);
  dbg_assert(new_head != NULL);
  dbg_assert(get_size(new_head) != 0);
  dbg_assert(get_alloc(new_head) == false);
  dbg_assert(valid_block_format(new_head) == true);

  new_head->next = *root;
  new_head->prev = NULL;
  (*root)->prev = new_head;
  *root = new_head;
}

/**
 * @brief 将ROOT所指向的链表的第一个元素移出链表，并将其返回
 *
 * @param root 指向链表的第一个元素指针
 * @return block_t* 链表的原第一个元素
 * @pre ROOT不能为NULL
 */
static block_t *pop_front(block_t **root) {
  dbg_assert(root != NULL);
  dbg_assert(&root != NULL);
  dbg_assert(check_free_block_aux(&root) == true);

  block_t *old_head = *root;
  old_head->next->prev = NULL;
  (*root) = old_head->next;
  return old_head;
}

/**
 * @brief 将BLOCK从链表中移出链表
 *
 * @note BLOCK不能为prologue block或者epilogue block
 *
 * @param block
 * @return block_t*
 * @pre BLOCK必须位于某个链表中，可以是头节点
 */
static void remove_block(block_t *block) {
  dbg_assert(block != NULL);
  dbg_assert(block->prev != NULL);
  dbg_assert(get_size(block) != 0);
  dbg_assert(get_alloc(block) == false);
  dbg_assert(check_free_block_aux(block) == true);

  // TODO 如果是升级为segregate list的话，那么这里的实现需要修改
  if(block->next != NULL){
    block->next->prev = block->prev;
  }
  if(block->prev != NULL){
    block->prev->next = block->next;
  }
}

/**
 * @brief 将BLOCK之前的元素移出链表
 *
 * @note BLOCK不可以是链表第一个元素
 *
 * @param block
 * @return block_t*
 */
static block_t *remove_before(block_t *block) {
  dbg_assert(block != NULL);
  dbg_assert(get_size(block) != 0);
  dbg_assert(get_alloc(block) == false);
  dbg_assert(check_free_block_aux(block) == true);

  block_t *removed = block->prev;
  if(removed->prev != NULL)
    removed->prev->next = block;
  block->prev = removed->prev;
  return removed;
}

/**
 * @brief 将BLOCK之后的元素移出链表
 *
 * @note BLOCK不可以是链表最后一个元素
 *
 * @param block
 * @return block_t*
 */
static block_t *remove_after(block_t *block) {
  dbg_assert(block != NULL);
  dbg_assert(get_size(block) != 0);
  dbg_assert(get_alloc(block) == false);
  dbg_assert(check_free_block_aux(block) == true);

  block_t *removed = block->next;
  if(removed->next != NULL)
    removed->next->prev = block;
  block->next = removed->next;
  return removed;
}

/**
 * @brief 遍历ROOT指向的链表，对其中所有元素调用AUX函数，执行失败即跳出循环。
 * 同时还会检查链表中的空置节点是否和堆中的空置节点数量相同
 *
 * @param root 指向链表第一个元素的指针
 * @param aux 辅助函数，接受一个block_t*类型的参数，返回一个bool表示操作是否成功
 * @param heap_count 堆中的节点数目
 */
static bool valid_list_iterate(block_t *root, bool aux(block_t *),
                               size_t heap_count) {
  bool validation = false;
  const char *message = NULL;
  size_t list_count = 0;
  for (block_t *curr = root; curr != NULL; curr = curr->next) {
    list_count++;
    validation = aux(curr);
    if (!validation) {
      message = "Aux fail";
      goto done;
    }
  }

  if (list_count != heap_count) {
    message = "List count not match with Heap count";
    goto done;
  }
done:
  if (!validation) {
    dbg_printf(message);
  }
  return validation;
}

/**
 * @brief 检查TAG的size字段和allocated bit是否和SIZE以及ALLOC给定值相符
 *
 * @note TAG指的是header或者footer
 *
 * @param tag 指向header或footer的指针
 * @param size 目标大小
 * @param alloc 目标分配情况
 * @return true 相符
 * @return false 不符
 */
static bool check_tag(word_t tag, size_t size, bool alloc) {
  return size == extract_size(tag) && alloc == extract_alloc(tag);
}

/**
 * @brief 检查ADDR所指代的地址是否指向堆中
 *
 * @param addr
 * @return true
 * @return false
 */
static bool check_address_in_heap(word_t addr) {
  return addr <= (word_t)mem_heap_hi() && addr >= (word_t)mem_heap_lo();
}

/**
 * @brief 检查WORD是否对齐双字，即低四位是否有东西
 *
 * @param word
 * @return true
 * @return false
 */
static bool check_word_align_dword(word_t word) {
  return (word & low_order_mask) == (word_t)0;
}

/**
 * @brief 检查BLOCK是否对齐：payload起点对齐16Byte、BLOCK底部对齐16Byte
 *
 * @param block
 * @return true
 * @return false
 */
static bool valid_block_align(block_t *block) {
  bool validation = false;
  const char *message = NULL;

  validation = check_word_align_dword((word_t)block->payload);
  if (!validation) {
    message = "payload not alignment";
    goto done;
  }

  validation = check_word_align_dword(find_next(block));
  if (!validation) {
    message = "block tail not alignment";
    goto done;
  }
done:
  if (!validation) {
    dbg_printf(message);
  }
  return validation;
}

/**
 * @brief 检查BLOCK的大小是否大于最小值
 *
 * @param block
 * @return true
 * @return false
 */
static bool check_block_size(block_t *block) {
  return get_size(block) >= min_block_size;
}

/**
 * @brief 检查BLOCK的header和footer是否相互匹配
 *
 * @param block
 * @return true
 * @return false
 */
static bool check_tags_match(block_t *block) {
  return block->header == block->footer;
}

/**
 * @brief 调用其他函数，总体检查BLOCK的格式
 *
 * @param block
 * @return true
 * @return false
 */
static bool valid_block_format(block_t *block) {
  bool validation = false;
  const char *message = NULL;

  validation = check_block_size(block);
  if (!validation) {
    message = "block smaller than min_block_size";
    goto done;
  }

  validation = check_tags_match(block);
  if (!validation) {
    message = "block header & footer not match";
    goto done;
  }

  validation = valid_block_align(block);
  if (!validation) {
    message = "block not align";
    goto done;
  }
done:
  if (!validation) {
    dbg_printf(message);
  }
  return validation;
}

/**
 * @brief 检查自己指向的节点的prev是否指向自己
 *
 * @param block
 * @return true
 * @return false
 * @pre prev & next都必须指向堆内
 */
static bool check_nodes_match(block_t *block) {
  return block == block->next->prev;
}

/**
 * @brief 调用其他函数，检查链表中指定节点的prev和next是否都是合法的地址。
 * 如果是链表头节点的话，那么prev可能为NULL
 *
 * @param block
 * @return true
 * @return false
 */
static bool check_node_addr(block_t *block) {
  return check_address_in_heap(block->next) &&
         (check_address_in_heap(block->prev) || block->prev == NULL);
}

/**
 * @brief 检查BLOCK是否是一个合法的链表节点
 *
 * @param block
 * @return true
 * @return false
 */
static bool valid_node(block_t *block) {
  bool validation = false;
  const char *message = NULL;

  // 检查next以及prev指针
  validation = check_node_addr(block);
  if (!validation) {
    message = "prev or next invalid";
    goto done;
  }

  // 检查header和footer是否匹配
  validation = check_nodes_match(block);
  if (!validation) {
    message = "next block's prev don't point to this block";
    goto done;
  }
done:
  if (!validation) {
    dbg_printf(message);
  }
  return validation;
}

/**
 * @brief 调试用辅助函数
 * 
 * @param block 
 * @return true 
 * @return false 
 */
static bool check_free_block_aux(block_t *block){
  return valid_block_format(block) && valid_node(block);
}

/*
 * ---------------------------------------------------------------------------
 *                        END SHORT HELPER FUNCTIONS
 * ---------------------------------------------------------------------------
 */

/******** The remaining content below are helper and debug routines ********/

/**
 * @brief 检查并确定是否需要将与BLOCK邻接的free block与之合并
 *
 * @note BLOCK必须处于空置状态且不位于任何链表中
 *
 * @par 此函数可能会操作链表
 *
 * @par free block时会被调用，需要分别处理四种不同的情况，
 * 处理后需根据新Block大小设置footer
 *
 * @par 四种不同的情况：
 * - 两边都已分配：只需将free list的头节点改成block即可；
 * - 左边或右边已释放：首先需要将该节点从free list中移除，随后将其与自身合并
 *   为一个新的Block，最后再将该Block移入free list；
 * - 两边都已释放：需要先将左右两个Block都从free list中移除，随后操作同上；
 *
 * @param[in] block 等待合并的Block
 * @return 合并之后的Block的地址，可能和参数一致
 * @pre get_alloc(block) == false，footer无需设置
 * @pre BLOCK不位于任何链表中
 * @pre BLOCK不可以是prologue block或者epilogue block
 */
static block_t *coalesce_block(block_t *block) {
  dbg_assert(get_alloc(block) == false);
  dbg_assert(get_size(block) != 0);

  // 获取堆中前后邻接的Block
  block_t *adj_front = find_prev(block);
  block_t *adj_back = find_next(block);
  bool adj_front_allocated = get_alloc(adj_front);
  bool adj_back_allocated = get_alloc(adj_back);

  if (adj_front_allocated) {
    if (adj_back_allocated) {
      // Case 1 两边都已分配
      push_front(&free_list_root, block);
    } else {
      // Case 2 右边已释放
      remove_block(adj_front);
      write_block(adj_front, get_size(adj_front) + get_size(block), false);
      push_front(&free_list_root ,adj_front);
    }
  } else {
    if (adj_back_allocated) {
    // Case 3 左边已释放
      remove_block(adj_back);
      write_block(block,  get_size(block) + get_size(adj_back), false);
      push_front(&free_list_root ,block);
    } else {
    // Case 4 两边都已释放
      remove_block(adj_front);
      remove_block(adj_back);
      write_block(adj_front, get_size(adj_front) + get_size(block) + get_size(adj_back), false);
      push_front(&free_list_root ,adj_front);
    }
  }
  return block;
}

/**
 * @brief 执行系统调用，将堆向上移动SIZE byte
 *
 * @note SIZE会被向上取整为双字的倍数
 *
 * @par 需要在堆末尾插入新Block时，需要这样做：
 * 1.next blcok的next为NULL，代表它是epilogue block，跳出循环；
 * 2.调用sbrk申请SIZE，注意实际移动的距离；
 * 3.如果位于堆最后的block是不是处于free状态，将其抽出free list、修改其大小
 *   并压入free list头部。注意为epilogue block留出空间；
 * 4.如果不是，将新申请的空间作为新Block压入free list顶部。同时确保
 *   epilogue block内容不变并修改其prev的next为新地址；
 *
 * @param[in] size 堆被向上移动的大小
 * @return 移动brk之后，堆最后一个Block的地址（不是payload）
 */
static block_t *extend_heap(size_t size) {
  void *bp;

  // Allocate an even number of words to maintain alignment
  size = round_up(size, dsize);
  if ((bp = mem_sbrk(size)) == (void *)-1) {
    return NULL;
  }

  /*
   * TODO: delete or replace this comment once you've thought about it.
   * Think about what bp represents. Why do we write the new block
   * starting one word BEFORE bp, but with the same size that we
   * originally requested?
   *
   * 原来的epilogue block的位置会被占掉，正好补偿了
   */

  // Initialize free block header/footer
  block_t *block = payload_to_header(bp);
  write_block(block, size, false);

  // Coalesce in case the previous block was free
  block = coalesce_block(block);

  // Create new epilogue header
  block_t *block_next = find_next(block);
  write_epilogue(block_next);

  // 更新链表头部为新Free Block
  free_list_root = block; 

  return block;
}

/**
 * @brief 检查并确定是否需要将BLOCK拆分为大小分别ASIZE和block size -
 * ASIZE的两个block
 *
 * @note 如果分割出来的大小小于min_block_size，那就不必分了
 *
 * @param[in] block 待拆分的block
 * @param[in] asize BLOCK的目标新大小
 * @pre ASIZE < get_size(BLOCK)
 * @pre asize对齐16 Byte
 */
static void split_block(block_t *block, size_t asize) {
  dbg_requires(get_alloc(block) == false);
  dbg_requires(asize <= get_size(block));
  dbg_requires(check_word_align_dword((word_t)asize));
  /* TODO: Can you write a precondition about the value of asize? */

  size_t block_size = get_size(block);

  if ((block_size - asize) >= min_block_size) {
    block_t *block_next;
    write_block(block, asize, true);

    block_next = find_next(block);
    write_block(block_next, block_size - asize, false);
    push_front(&free_list_root, block_next);

    dbg_ensures(block_next == free_list_root);
  }

  dbg_ensures(get_alloc(block));
}

/**
 * @brief 在堆中寻找一个大小大于等于ASIZE的块
 *
 * @par first fit
 *
 * @param[in] asize 目标大小
 * @return 块的地址，如果没有找到则是NULL
 */
static block_t *find_fit(size_t asize) {
  block_t *block;

  for (block = free_list_root; get_size(block) > 0; block = block->next) {
    if (!(get_alloc(block)) && (asize <= get_size(block))) {
      return block;
    }
  }
  return NULL; // no fit found
}

/**
 * @brief 检查堆的不变性是否始终被满足
 *
 * @par Heap check：
 * - epilogue & prologue blocks 格式检查（见下）；
 * - Coalesce检查：堆中不可以有任何两个连续的Free Block存在；
 *
 * @par List check：
 * - 前后两个Block需具有正确的next/previous指向；
 * - 所有指针都位于mem heap lo() & mem heap high()之间；
 * - 遍历堆得到的Free block数目应该和遍历free list得到的数目一致；
 * - segregated list相关（ @todo ）
 *
 * @par Block check：
 * - Block地址均对齐16Byte；
 * - Block都在Heap的边界之内；
 * - Free之后Block的allocate bit应该被合理设置；
 * - 每个Block的Header和Footer：
 *    - 大小是大于等于Block的最小值；
 *    - prev和next是否具有一致性；
 *    - allocate bit是否符合实际情况；
 *    - Header和Footer是否相互匹配；
 *
 * @par free list方面，epilogue block需保持如下不变性：
 * - next元素始终为NULL：可用于检测是否到达free list的末尾；
 * - prev元素始终指向block_t：可将初次插入以及后续插入
 *   平凡化为同一种情况，将其当作普通的block修改指针即可；
 * -
 * 由于堆初始情况下即包含有一个大小为chunksize的block，因此prev元素不可为NULL；
 *
 * @par coalesce block方面，epilogue block和prologue blcok都需保持
 * allocated bit为1，以便将边界coalesce情况化为平凡情况
 *
 * @par free list需保持如下不变性：
 * - 头部节点prev必然为NULL；
 * - 尾部节点必须是epilogue block；
 *
 *
 * @param[in] line 被调用时的行号
 * @return 堆是否满足不变性
 */
bool mm_checkheap(int line) {
  /*
   * You will need to write the heap checker yourself.
   * Please keep modularity in mind when you're writing the heap checker!
   *
   * As a filler: one guacamole is equal to 6.02214086 x 10**23 guacas.
   * One might even call it...  the avocado's number.
   *
   * Internal use only: If you mix guacamole on your bibimbap,
   * do you eat it with a pair of chopsticks, or with a spoon?
   */

  bool valid = false;
  const char *message = NULL;

  // 检查prologue block格式
  valid = check_tag(*find_prev_footer(heap_start), 0, true);
  if (!valid) {
    message = "prologue block format error!";
    goto done;
  }

  // 检查free list中所有的block
  block_t *curr;
  size_t count = 0;

  // 检查堆中的每一个块的格式是否合法，同时统计其中free block的数目
  for (curr = heap_start; get_size(curr) != 0; curr = find_next(curr)) {
    valid = valid_block_format(curr);
    if (!valid) {
      message = "Block invalid";
      goto done;
    }

    if (!get_alloc(curr)) {
      count++;
    }
  }

  // 检查epilogue block是否合法
  valid = check_tag(*find_prev_footer(curr), 0, true);
  if (!valid) {
    message = "epilogue Block invalid";
    goto done;
  }

  // 遍历链表中的所有节点，检查它们是否合法
  valid = valid_list_iterate(free_list_root, valid_node, count);
  if (!valid) {
    message = "List invalid";
    goto done;
  }
done:
  if (!valid) {
    dbg_printf(message);
  }
  return valid;
}

/**
 * @brief 初始化堆
 *
 * @par 初始状况下的堆长度为64Byte (4 DWord) + chunksize：
 * - DWord1：prologue block的footer；
 * - DWord2：epilogue block的header；
 * - DWord3：epilogue block的prev；
 * - DWord4：epilogue block的next；
 * - chunksize：堆初始的空余空间，可被直接使用；
 * 它们的“size”字段都为0，用于标识
 *
 * @return
 */
bool mm_init(void) {
  // Create the initial empty heap
  word_t *start = (word_t *)(mem_sbrk(2 * wsize));

  if (start == (void *)-1) {
    return false;
  }

  /*
   * TODO: delete or replace this comment once you've thought about it.
   * Think about why we need a heap prologue and epilogue. Why do
   * they correspond to a block footer and header respectively?
   *
   * 主要的目的是用来标识堆的边界
   */

  start[0] = pack(0, true); // Heap prologue (block footer)
  start[1] = pack(0, true); // Heap epilogue (block header)

  // Heap starts with first "block header", currently the epilogue
  heap_start = (block_t *)&(start[1]);

  block_t *first_block = NULL;

  // Extend the empty heap with a free block of chunksize bytes
  if ((first_block = extend_heap(chunksize)) == NULL) {
    return false;
  }

  return true;
}

/**
 * @brief 获取一个指定大小的Block，可能调用sbrk
 *
 * @par 需执行的操作如下：
 * 1.find_fit：遍历free list，寻找合适的free block；
 *   1.找到了：将其移出free list；
 *   2.没有找到：调用extend_heap拓展堆；
 * 2.split_block：根据占用大小对其进行分割；
 *
 * @param[in] size 目标payload的大小，不一定是倍数
 * @return 合适payload的地址
 * @post 返回地址需对齐Dword
 */
void *malloc(size_t size) {
  dbg_requires(mm_checkheap(__LINE__));

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
  asize = round_up(size + dsize, dsize);

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

  // 将block从free list中移除
  remove_block(block);

  // Mark block as allocated
  size_t block_size = get_size(block);
  write_block(block, block_size, true);

  // Try to split the block if too large
  split_block(block, asize);

  bp = header_to_payload(block);

  dbg_ensures(mm_checkheap(__LINE__));
  return bp;
}

/**
 * @brief 释放目标BP指向的block
 *
 * @par 需执行的操作如下：
 * 1.将指定Block从free list中移出；
 * 2.将其状态标记为free；
 * 3.Coalesce邻接Block；
 * 4.将新free block插入free list头部；
 *
 * @param[in] bp
 * @pre 鉴于payload的地址必对齐16位，似乎可以利用这一特性
 * @post header & footer的allocated bit都被合理设置
 * @post 位于free list的头部
 * @post 堆中不可有连续的free block
 */
void free(void *bp) {
  dbg_requires(mm_checkheap(__LINE__));

  if (bp == NULL) {
    return;
  }

  block_t *block = payload_to_header(bp);
  size_t size = get_size(block);

  // The block should be marked as allocated
  dbg_assert(get_alloc(block));

  // Mark the block as free
  write_block(block, size, false);

  // Try to coalesce the block with its neighbors
  block = coalesce_block(block);

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