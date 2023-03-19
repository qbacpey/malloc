/**
 * @file mm.c
 * @brief A 64-bit struct-based implicit free list memory allocator
 *
 * 15-213: Introduction to Computer Systems
 *
 * Segregate List实现：
 *
 * Placement policy：best fit
 * Splitting policy：不少于最小块的大小即可
 * Coalescing policy：immediate coalesce
 * Insertion policy：LIFO & Address order
 * Eliminating Footers：yes
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

/** @brief 用于作为链表末尾的标识符，链表最后一个元素的next字段是这个东西 */
#define END_OF_LIST ((void *)~0x0)

/** @brief 一个Cluster中Cluster Block的数目 */
#define CLUSTER_BLOCK_COUNT 6

/** @brief Word and header size (bytes) */
static const size_t wsize = sizeof(word_t);

/** @brief Double word size (bytes) */
static const size_t dsize = 2 * wsize;

/** @brief Minimum block size (bytes)
 *
 * header + prev pointer + next pointer + footer
 * 不允许Payload为0
 */
static const size_t min_block_size = 4 * wsize;

/**
 * @brief header
 *
 */
static const size_t overhead_size = wsize;

/**
 * sbrk一次移动的最小长度，现在是4KB
 * 需要在利用率和吞吐量之间平衡
 * (Must be divisible by dsize) sta
 *
 */
static const size_t chunksize = (1 << 12);

/**
 * @brief cluster 整体的大小
 *
 */
static const size_t cluster_size = 8 * dsize;

/**
 * @brief 一个cluster block的大小
 *
 */
static const size_t cluster_block_size = dsize;

/**
 * @brief 一个cluster block的大小
 *
 */
// static const size_t cluster_block_payload_size = wsize;

/**
 * @brief Flag field bit的数目
 *
 */
static const uint8_t flag_bit_count = 4;

/**
 * @brief Header中被用作size字段的Bit的开始位置n
 *
 */
static const uint8_t size_bit_count = 64 - flag_bit_count;

/**
 * @brief Cluster Block Header中被用作num字段的Bit的开始位置
 *
 */
const uint8_t num_bit_count = size_bit_count - flag_bit_count;

/**
 * @brief Flag字段的低位（0），用于计算当前Block是否被分配
 */
static const word_t alloc_mask = (word_t)0x1 << size_bit_count;

/**
 * @brief Flag字段的低位（1），用于计算当前Block之前的Block是否被分配
 *
 */
static const word_t front_alloc_mask = (word_t)0x2 << size_bit_count;

/**
 * @brief Flag字段中第三位的掩码
 *
 */
static const word_t cluster_mask = (word_t)0x4 << size_bit_count;

/**
 * @brief word最后一个Byte的前四个Bit的mask
 *
 */
static const word_t cluster_num_mask = (word_t)0xF << num_bit_count;

/**
 * @brief Cluster中六个Cluster Block的分配情况Bit
 *
 */
static const word_t cluster_alloc_field_mask = 0x000000000000003F;

/**
 * @brief Flag field为word的最后四个Bit
 *
 */
// static const word_t flag_field_mask = (word_t)0xF << size_bit_count;

/**
 * @brief 低四位掩码
 *
 */
static const word_t low_four_bit_mask = (word_t)0xF;

/**
 * 用于计算Block大小的掩码，单位是Byte
 */
// static const word_t size_mask = ~flag_field_mask;

/** @brief 用于定位ASIZE中间8（0~255）位的掩码（需要先进行移动位置操作）*/
static const uint8_t group_mask = 0xFF;

/** @brief 从Header的第一个Byte开始，每一个Bit对应一个Cluster Block的分配情况 */
#define CLUSTER_B1 0x0000000000000001
#define CLUSTER_B2 0x0000000000000002
#define CLUSTER_B3 0x0000000000000004
#define CLUSTER_B4 0x0000000000000008
#define CLUSTER_B5 0x0000000000000010
#define CLUSTER_B6 0x0000000000000020
#define CLUSTER_FULL 6

/** @brief 一个Cluster中有6个大小为16Byte的Cluster Block */
static const word_t cluster_block_alloc_mask_table[CLUSTER_BLOCK_COUNT] = {
    CLUSTER_B1, CLUSTER_B2, CLUSTER_B3, CLUSTER_B4, CLUSTER_B5, CLUSTER_B6};

/**
 * @brief cluster共有多少种不同的分配状态
 *
 */
#define CLUSTER_ALLOC_STATUS 64

/**
 * @brief lookup table，用于快速找到一个6 Bit数中的第一个0的Index
 *
 */
static const uint8_t cluster_alloc_to_num[] = {
    0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 4, 0, 1, 0, 2,           0, 1,
    0, 3, 0, 1, 0, 2, 0, 1, 0, 5, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1,           0, 2,
    0, 1, 0, 4, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, CLUSTER_FULL};

/**
 * @brief 根据Cluster的Alloc field，确定其中有几个Cluster
 * Block已分配（计算其中1的数目）
 *
 */
static const uint8_t cluster_alloc_to_bit_count[] = {
    0, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 3, 2, 3, 3, 4, 1, 2, 2, 3, 2, 3,
    3, 4, 2, 3, 3, 4, 3, 4, 4, 5, 1, 2, 2, 3, 2, 3, 3, 4, 2, 3, 3, 4,
    3, 4, 4, 5, 2, 3, 3, 4, 3, 4, 4, 5, 3, 4, 4, 5, 4, 5, 5, 6};

#define G_EMPTY 255
#define G_16 0
#define G_32 1
#define G_48 2
#define G_64 3
#define G_128 4
#define G_192 5
#define G_256 6
#define G_384 7
#define G_512 8
#define G_1024 9
#define G_1536 10
#define G_2048 11
#define G_4096 12
#define G_INF 13

/** @brief 如果ASIZE比这个数大，那么该Block就有多种不同大小的Block */
#define MAX_SINGLE_BLOCK_GROUP 64
#define MAX_BLOCK_GROUP 4096

/**
 * @brief ASIZE与list_table的INDEX之间映射的数组，
 *        映射完毕后可以在list_table寻址对应list的root
 *
 * @note 执行映射操作之前需要先查看ASIZE是不是大于1024。
 *       ASIZE必须对齐16Byte之后截取高4位之后的五位数字（0~63），
 *       左移4位，再到数组中进行寻址
 *
 * @par 数组中各下标含有如下内容：
 * + 0：asize = 4096，为G_4096；
 * + 1：asize = 16，为G_16；
 * + 2：asize = 32，为G_32；
 * + 3：asize = 48，为G_48；
 * + 4：asize = 64，为G_64；
 * + 5 ~ 8：asize = (64, 128]，为G_128；
 * + 9 ~ 12：asize = (128, 192]，为G_192；
 * + 13 ~ 16：asize = (192, 256]，为G_256；
 * + 17 ~ 24：asize = (256, 384]，为G_384；
 * + 25 ~ 32：asize = (384, 512]，为G_512；
 * + 33 ~ 64：asize = (768, 1024]，为G_1024；
 * + 65 ~ 96：asize = (1024, 1536]，为G_1536；
 * + 97 ~ 128：asize = (1536, 2048]，为G_2048；
 * + 129 ~ 255：asize = (2048, 4096)，为G_4096；
 *
 */
static const uint8_t asize_to_index[] = {
    G_4096, G_16,   G_32,   G_48,   G_64,   G_128,  G_128,  G_128,  G_128,
    G_192,  G_192,  G_192,  G_192,  G_256,  G_256,  G_256,  G_256,  G_384,
    G_384,  G_384,  G_384,  G_384,  G_384,  G_384,  G_384,  G_512,  G_512,
    G_512,  G_512,  G_512,  G_512,  G_512,  G_512,  G_1024, G_1024, G_1024,
    G_1024, G_1024, G_1024, G_1024, G_1024, G_1024, G_1024, G_1024, G_1024,
    G_1024, G_1024, G_1024, G_1024, G_1024, G_1024, G_1024, G_1024, G_1024,
    G_1024, G_1024, G_1024, G_1024, G_1024, G_1024, G_1024, G_1024, G_1024,
    G_1024, G_1024, G_1536, G_1536, G_1536, G_1536, G_1536, G_1536, G_1536,
    G_1536, G_1536, G_1536, G_1536, G_1536, G_1536, G_1536, G_1536, G_1536,
    G_1536, G_1536, G_1536, G_1536, G_1536, G_1536, G_1536, G_1536, G_1536,
    G_1536, G_1536, G_1536, G_1536, G_1536, G_1536, G_1536, G_2048, G_2048,
    G_2048, G_2048, G_2048, G_2048, G_2048, G_2048, G_2048, G_2048, G_2048,
    G_2048, G_2048, G_2048, G_2048, G_2048, G_2048, G_2048, G_2048, G_2048,
    G_2048, G_2048, G_2048, G_2048, G_2048, G_2048, G_2048, G_2048, G_2048,
    G_2048, G_2048, G_2048, G_4096, G_4096, G_4096, G_4096, G_4096, G_4096,
    G_4096, G_4096, G_4096, G_4096, G_4096, G_4096, G_4096, G_4096, G_4096,
    G_4096, G_4096, G_4096, G_4096, G_4096, G_4096, G_4096, G_4096, G_4096,
    G_4096, G_4096, G_4096, G_4096, G_4096, G_4096, G_4096, G_4096, G_4096,
    G_4096, G_4096, G_4096, G_4096, G_4096, G_4096, G_4096, G_4096, G_4096,
    G_4096, G_4096, G_4096, G_4096, G_4096, G_4096, G_4096, G_4096, G_4096,
    G_4096, G_4096, G_4096, G_4096, G_4096, G_4096, G_4096, G_4096, G_4096,
    G_4096, G_4096, G_4096, G_4096, G_4096, G_4096, G_4096, G_4096, G_4096,
    G_4096, G_4096, G_4096, G_4096, G_4096, G_4096, G_4096, G_4096, G_4096,
    G_4096, G_4096, G_4096, G_4096, G_4096, G_4096, G_4096, G_4096, G_4096,
    G_4096, G_4096, G_4096, G_4096, G_4096, G_4096, G_4096, G_4096, G_4096,
    G_4096, G_4096, G_4096, G_4096, G_4096, G_4096, G_4096, G_4096, G_4096,
    G_4096, G_4096, G_4096, G_4096, G_4096, G_4096, G_4096, G_4096, G_4096,
    G_4096, G_4096, G_4096, G_4096, G_4096, G_4096, G_4096, G_4096, G_4096,
    G_4096, G_4096, G_4096, G_4096};

static const uint16_t index_to_asize[] = {128, 32,  48,   64,   128,  192, 256,
                                          384, 512, 1024, 1536, 2048, 4096};

typedef struct list_elem {
  /** @brief 指向free list中后一个block的指针 */
  struct list_elem *next;
  /** @brief 指向free list中前一个block的指针 */
  struct list_elem *prev;
} list_elem_t;

/** @brief Represents the header and payload of one block in the heap */
typedef struct block {
  /** @brief Header contains size + allocation flag */
  word_t header;

  /**
   * @brief A pointer to the block payload.
   *
   * We don't know what the size of the payload will be, so we will declare
   * it as a zero-length array, which is a GCC compiler extension. This will
   * allow us to obtain a pointer to the start of the payload.
   *
   * 可以通过get_body(block)获取payload的地址
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
  union body {
    list_elem_t list_elem;
    char payload[0];
  } body;

  /*
   * TODO: delete or replace this comment once you've thought about it.
   * Why can't we declare the block footer here as part of the struct?
   * Why do we even have footers -- will the code work fine without them?
   * which functions actually use the data contained in footers?
   */
} block_t;

/**
 * @brief
 * Minimum Block优化：
 *  1. 添加了一个由16 Byte Block构成的集群链表:
 *    1. 集群大小为128 Byte：
 *      1. 集群Block的整体结构和普通Free
 *         Block一样。头尾各自是Header和Footer，无论什么情况都不将它们移除。
 *         Header第一个Byte的低4Bit和普通的Header一样，第三个Bit（cluster
 * bit）会被置1用于表示集群， 只有内部的所有Implicit
 * Block都被释放之后，Allocated Bit才被标记为1，其他规则和普通Block一致。
 *         Header第五个Byte用于表示集群Block内部Implicit
 * Block的分配情况，从最底位开始，一直到第六位。
 *         Header的后面则是`list_elem_t`结构体，依然使用双向链表维护集群Block；
 *       2. 除了32 Byte的Overhead，剩余的96 Byte由6个双字对齐的Implicit
 * Block构成。 15 Byte的Payload后接1
 * Byte的Header作为其所有内容，Header保存Block于集群内的编号；
 *    2. LIFO维护，因此只需要实现链表头部插入函数即可；
 *      1. 一旦释放了集群中的任意一个Block，都需要将集群推入链表头部
 *    3.移除元素有两种情况：
 *      1.分配Block时，只有当集群中没有空Block时才将集群Block从根节点中移除，否则只是操作集群Header
 *         同时，初次在集群内部分配Block时要将集群的allocated bit设置为1；
 *      2.合并Block的时候可能要将集群从链表中移除，只有当allocated
 * bit=0（无任何分配Block）时才可合并 合并时需要检查cluster bit，将其当成128
 * Byte的Block合并；
 *
 */

/** @brief 14个Segregate List */
#define LIST_TABLE_SIZE 14

/**
 * @brief 堆第一个Block的起始位置，类型为block_t *，mem_heap_lo() + prologue
 *
 * @note 不再作为标识堆是否被初始化的依据
 *
 */
#define HEAP_START (block_t *)(mem_heap_lo() + wsize)

/* Global variables */

/**
 * @brief free list头节点
 *
 * @par 链表头结点的操作有些特殊：
 * 1.向其中插入节点的时候可以将此指针**看成是**位于某个list_elem_t结构体中，
 *   这样无论是向链表中插入元素还是移除元素，如果遇到需要接收一个
 *   list_elem_t *进而对其中的prev和next指针进行操作的函数，那么就需要
 *   获取根节点的地址，把根节点所在的地址当成是一个指向list_elem_t的指针
 *   就可以像普通节点一样对根节点进行操作了。
 *
 *   需要注意的是，无论是移除操作还是插入操作，由于这仅仅是一个有next半边的
 *   list_elem_t，因此只能调用insert_next函数，被插入者是链表根节点
 *
 *   移除操作也只能把其他节点当成是主体，不能把这个虚拟的list_elem_t当成是主体
 *
 * 2.Check函数也需要适时更新，第一是现在的prev指针有可能指向堆外，也就是
 *   free_list_root的地址，第二是需要检查所有链表的最后一个next指针是不是
 *   END_OF_LIST
 *
 */
static list_elem_t *list_table[LIST_TABLE_SIZE];

/**
 * @brief 用于表示对应链表是否为空
 *
 */
static bool list_no_empty[LIST_TABLE_SIZE];
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

/* Heap checking function */

static bool check_free_block_aux(block_t *);
static bool valid_block_format(block_t *);
static bool check_word_align_dword(word_t);
static bool check_word_align_word(word_t);
static bool check_address_in_heap(word_t);
static bool check_addr_is_root(list_elem_t *);
static bool check_size_list(uint8_t, list_elem_t *);
static bool check_is_node(block_t *);

/* List pointer operation */

static inline list_elem_t *get_prev(list_elem_t *);
static inline void set_prev(list_elem_t *, list_elem_t *);
static inline list_elem_t *get_next(list_elem_t *);
static inline void set_next(list_elem_t *, list_elem_t *);

/* List operation */

static void push_front(list_elem_t *root, list_elem_t *);
static void push_order(list_elem_t *root, list_elem_t *);
static void push_single(list_elem_t *root, list_elem_t *);
static void push_list(uint8_t table_index, list_elem_t *list_elem);
static void remove_list_elem(list_elem_t *);
static list_elem_t *get_list_by_index(uint8_t);
static list_elem_t *pop_single(list_elem_t *root);

/* Block fit */

static block_t *find_good_fit(size_t, uint8_t);
static block_t *find_first_fit(size_t, uint8_t);
static block_t *find_fit(size_t);

static block_t *find_next(block_t *);
static block_t *find_heap_by_cmp(block_t *, bool cmp(block_t *, block_t *));
static list_elem_t *find_list_by_cmp(list_elem_t *, list_elem_t *,
                                     bool cmp(list_elem_t *, list_elem_t *));
static inline bool cmp_back_is_block(block_t *block, block_t *curr);
static inline bool cmp_insert_after_list_elem(list_elem_t *block,
                                              list_elem_t *curr);

/* Declaration end */

/* Functions table start */

/**
 * @brief 用于向链表中push block的函数类型
 *
 */
typedef void (*push_func_t)(list_elem_t *, list_elem_t *);

/**
 * @brief 用于在INDEX（G_XX）和对应的push函数之间提供映射。
 *        所有链表直接通过push_front实现，不使用push_order
 *        使用该方式对提升内存利用率没有任何提升
 *
 */
static const push_func_t index_to_push_func[] = {
    push_single, push_front, push_front, push_front, push_front,
    push_front,  push_front, push_front, push_front, push_front,
    push_front,  push_front, push_front, push_front};

/**
 * @brief 用于在链表中寻找合适Block的函数类型
 *
 */
typedef block_t *(*fit_func_t)(size_t, uint8_t);

/**
 * @brief 根据List的不同，使用此数组选择不同的Fit函数
 *
 */
static const fit_func_t index_to_fit_func[] = {
    find_first_fit, find_first_fit, find_first_fit, find_first_fit,
    find_good_fit,  find_good_fit,  find_good_fit,  find_good_fit,
    find_good_fit,  find_good_fit,  find_good_fit,  find_good_fit,
    find_good_fit,  find_first_fit};

/* Functions table end */

/**
 * @brief Returns the maximum of two integers.
 * @param[in] x
 * @param[in] y
 * @return `x` if `x > y`, and `y` otherwise.
 */
static size_t max(size_t x, size_t y) { return (x > y) ? x : y; }

/**
 * @brief 将B的布尔值反转
 *
 * @param b
 * @return true
 * @return false
 */
static bool flip(bool b) { return b != true; }

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
 * TODO 查表优化
 *
 * The allocation status is packed into the lowest bit of the word.
 *
 * @param[in] size The size of the block being represented
 * @param[in] alloc True if the block is allocated
 * @return The packed value
 */
static inline word_t pack_regular(size_t size, bool alloc, bool front_alloc) {
  word_t word = size >> flag_bit_count;
  if (alloc) {
    word |= alloc_mask;
  }
  if (front_alloc) {
    word |= front_alloc_mask;
  }
  return word;
}

/**
 * @brief 同上，只不过会在此函数专用于写入cluster
 *
 * @param alloc 同pack_regular
 * @param front_alloc 同pack_regular
 * @param cluster 用于判断是否需要置cluster bit
 * @return word_t
 */
static inline word_t pack_cluster(bool alloc, bool front_alloc) {
  static const size_t size = cluster_size >> flag_bit_count;
  word_t word = size;
  if (alloc) {
    word |= alloc_mask;
  }
  if (front_alloc) {
    word |= front_alloc_mask;
  }
  word |= cluster_mask;
  return word;
}

/**
 * @brief 将NUM打包到一个Word里，作为Cluster
 * Block的Header。NUM将会被放在返回值的第一个Byte的后四个Bit
 *
 * @param num
 * @return word_t
 */
static inline word_t pack_cluster_block_header(uint8_t num) {
  const static word_t num_to_mask[] = {
      (word_t)0x0 << num_bit_count, (word_t)0x1 << num_bit_count,
      (word_t)0x2 << num_bit_count, (word_t)0x3 << num_bit_count,
      (word_t)0x4 << num_bit_count, (word_t)0x5 << num_bit_count};
  word_t header = 0;
  header |= cluster_mask;
  header |= num_to_mask[num];
  return header;
}

/**
 * @brief 利用指定HEADER第最后一个Byte的前四个Bit，获取该Cluster Block的标号
 *
 * @param header
 * @return uint8_t
 */
static inline uint8_t extract_cluster_block_num(word_t header) {
  return (header & cluster_num_mask) >> num_bit_count;
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
static size_t extract_size(word_t word) { return (word << flag_bit_count); }

/**
 * @brief Extracts the size of a block from its header.
 * @param[in] block
 * @return The size of the block
 */
static inline size_t get_size(block_t *block) {
  return extract_size(block->header);
}

/**
 * @brief Get the payload object
 *
 * @param block
 * @return void*
 */
static void inline *get_body(block_t *block) { return (void *)&(block->body); }

/**
 * @brief Given a payload pointer, returns a pointer to the corresponding
 *        block.
 * @param[in] bp A pointer to a block's payload
 * @return The corresponding block
 */
static block_t *payload_to_header(void *bp) {
  return (block_t *)((char *)bp - offsetof(block_t, body));
}

/**
 * @brief Given a block pointer, returns a pointer to the corresponding
 *        payload.
 * @param[in] block
 * @return A pointer to the block's payload
 */
static void *header_to_payload(block_t *block) { return get_body(block); }

/**
 * @brief Given a block pointer, returns a pointer to the corresponding
 *        footer. Block的倒数第一个Word
 * @param[in] block
 * @return A pointer to the block's footer
 */
static word_t *header_to_footer(block_t *block) {
  return (word_t *)((void *)block + get_size(block) - overhead_size);
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
static size_t get_body_size(block_t *block) {
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
static bool extract_alloc(word_t word) {
  return (word & alloc_mask) != 0;
  ;
}

/**
 * @brief Returns the allocation status of the front block of a given header
 * value.
 *
 * This is based on the second lowest bit of the header value.
 *
 * @param word
 * @return The allocation status correpsonding to the word
 */
static bool extract_front_alloc(word_t word) {
  // 不等于0代表该Bit为1，前一个Block处于Alloc
  return (word & front_alloc_mask) != 0;
}

/**
 * @brief Returns weather the header is a cluster block header.
 *
 * This is based on the third lowest bit of the header value.
 *
 * @param word
 * @return bool
 */
static bool extract_cluster(word_t word) {
  return (word & cluster_mask) != 0;
  ;
}

/**
 * @brief Set the cluster bit of WORD to 1
 *
 * @param word
 * @return true
 * @return false
 */
static void set_cluster(word_t *word) { *word |= cluster_mask; }

/**
 * @brief Returns the allocation status of a block, based on its header.
 * @param[in] block
 * @return The allocation status of the block
 */
static bool get_alloc(block_t *block) { return extract_alloc(block->header); }

/**
 * @brief Returns the allocation status of the front block of a block, based on
 * its header.
 *
 * @param block
 * @return Front block's allocation status of the block
 */
static bool get_front_alloc(block_t *block) {
  return extract_front_alloc(block->header);
}

/**
 * @brief Returns whether the block is a cluster block.
 *
 * @param block
 * @return true
 * @return false
 */
static bool get_cluster(block_t *block) {
  return extract_cluster(block->header);
}

/**
 * @brief 获取BLOCK的alloc字段（即第一个Cluster的最后一个Word）
 *
 * TODO 改成2
 *
 * @param block
 * @return word_t
 */
static word_t *cluster_alloc_field(block_t *block) {
  return (word_t *)block + 15;
}

/**
 * @brief 获取Cluster的分配情况Field
 *
 * @param block
 * @return uint8_t
 */
static uint8_t get_cluster_alloc_field(block_t *block) {
  dbg_assert(get_cluster(block) == true);
  return *cluster_alloc_field(block) & cluster_alloc_field_mask;
}

/**
 * @brief Get the NUM cluster block alloc state of BLOCK
 *
 * @param block
 * @param num Cluster Block在BLOCK中的编号
 * @return true
 * @return false
 */
static bool get_cluster_block_alloc(block_t *block, uint8_t num) {
  dbg_assert(get_cluster(block) == true);
  dbg_assert(num < CLUSTER_BLOCK_COUNT);

  return (get_cluster_alloc_field(block) &
          cluster_block_alloc_mask_table[num]) != 0;
}

/**
 * @brief 判断BLOCK中是否有任何Cluster block已分配
 *
 * @param block
 * @return true
 * @return false
 */
static bool deduce_cluster_empty(block_t *block) {
  dbg_assert(get_cluster(block) == true);

  return (get_cluster_alloc_field(block) & cluster_alloc_field_mask) == 0;
}

/**
 * @brief 判断BLOCK中是否所有Cluster block已分配
 *
 * @param block
 * @return true
 * @return false
 */
static bool deduce_cluster_full(block_t *block) {
  dbg_assert(get_cluster(block) == true);

  return (get_cluster_alloc_field(block) & cluster_alloc_field_mask) ==
         cluster_alloc_field_mask;
}

/**
 * @brief Set the alloc state of the NUM cluster block of BLOCK to ALLOC
 *
 * @param block
 * @param num 需要改变allocated bit的cluster block的标号
 * @param alloc 新的分配状态
 */
static void set_cluster_block_alloc(block_t *block, uint8_t num, bool alloc) {
  dbg_assert(get_cluster(block) == true);
  dbg_assert(num < CLUSTER_BLOCK_COUNT);
  if (alloc)
    *cluster_alloc_field(block) |= cluster_block_alloc_mask_table[num];
  else
    *cluster_alloc_field(block) &= ~(cluster_block_alloc_mask_table[num]);
}

/**
 * @brief 将TAG指向的字段的front_alloc字段标记为FRONT_ALLOC
 *
 * @param tag 目标TAG
 * @param front_alloc 目标布尔值
 */
static void set_front_alloc(word_t *tag, bool front_alloc) {
  if (front_alloc)
    *tag |= front_alloc_mask;
  else
    *tag &= ~front_alloc_mask;
}

/**
 * @brief 将位于BLOCK后边的邻接Block的front alloc bit设置为FRONT_BLOCK
 *
 * @param block
 * @param front_alloc
 */
static void set_front_alloc_of_back_block(block_t *block, bool front_alloc) {
  block_t *next = find_next(block);
  set_front_alloc(&(next->header), front_alloc);
  // 只有在邻接的下一个Block未被分配的时候，才设置footer
  if (!get_alloc(next)) {
    set_front_alloc(header_to_footer(next), front_alloc);
  }
}

/**
 * @brief 打印BLOCK中的各项数据
 *
 * @param block
 */
static void print_block(block_t *block) {
  printf("\nBlock address:\t\t\t %p\n", block);
  printf("Block header:\t\t\t 0x%09lx\n", block->header);
  printf("Block footer:\t\t\t 0x%09lx\n", *header_to_footer(block));
  printf("Block Size:\t\t\t %ld\n", get_size(block));
  printf("Block alloc:\t\t\t %s\n",
         get_alloc(block) == true ? "true" : "false");
  printf("Block front alloc:\t\t %s\n",
         get_front_alloc(block) == true ? "true" : "false");
  printf("Block is a cluster:\t\t %s\n",
         get_cluster(block) == true ? "true" : "false");
  if (get_cluster(block)) {
    printf("Cluster status:\t\t\t %s\n",
           deduce_cluster_empty(block)
               ? "empty"
               : deduce_cluster_full(block) ? "full" : "no empty");
    for (uint8_t i = 0; i != CLUSTER_BLOCK_COUNT; i++) {
      printf("Cluster Block %d alloc:\t\t %s\n", i,
             get_cluster_block_alloc(block, i) == true ? "true" : "false");
    }
  }
}

/**
 * @brief Writes an epilogue header at the given address.
 *
 * The epilogue header has size 0, and is marked as allocated.
 *
 * @param[out] block The location to write the epilogue header
 * @pre block == mem_heap_hi() - 7
 */
static void write_epilogue(block_t *block, bool front_alloc) {
  dbg_requires(block != NULL);
  dbg_requires((char *)block == mem_heap_hi() - 7);

  block->header = pack_regular(0, true, front_alloc);
}

/**
 * @brief Writes a block starting at the given address.
 * @pre size >= min_block_size
 * @pre size 对齐 16Byte
 *
 * @note 大多数情况下此函数的调用语句之后都会跟随一个
 * set_front_alloc_of_back_block函数调用
 *
 * @par
 * This function writes both a header and footer, where the location of the
 * footer is computed in relation to the header.
 *
 * 有一个重要事实是，如果是分配Block的话，footer会被覆盖掉
 *
 * TODO: Are there any preconditions or postconditions?
 *
 * @param[out] block The location to begin writing the block header
 * @param[in] size The size of the new block
 * @param[in] alloc The allocation status of the new block
 * @param[in] front_alloc The allocation status of front block of the new block
 */
static void write_block(block_t *block, size_t size, bool alloc,
                        bool front_alloc) {
  dbg_requires(block != NULL);
  dbg_requires(size >= min_block_size);
  dbg_requires(check_word_align_dword((word_t)size));

  block->header = pack_regular(size, alloc, front_alloc);
  // 只有Free block才有footer
  if (!alloc) {
    word_t *footerp = header_to_footer(block);
    *footerp = pack_regular(size, alloc, front_alloc);
  }
}

/**
 * @brief 获取BLOCK的第NUM个Cluster Block
 *
 * @param block
 * @param num
 * @return void*
 */
static inline void *get_cluster_block(block_t *block, uint8_t num) {
  dbg_requires(block != NULL);
  dbg_assert(get_cluster(block) == true);
  dbg_assert(num < CLUSTER_BLOCK_COUNT);
  // TODO 优化
  return (void *)block + dsize + num * dsize;
}

/**
 * @brief 利用Cluster Block的地址计算其Payload的地址
 *
 * @param cluster_block
 * @return void*
 */
static inline void *cluster_block_to_payload(void *cluster_block) {
  return cluster_block + wsize;
}

/**
 * @brief 在BLOCK上创建一个Cluster，将其压入G_16链表中
 *
 * @note BLOCK的大小必须是128 Byte且已分配并不位于任何表中
 *
 * @param block
 * @param size
 * @param alloc
 * @param front_alloc
 */
static void create_cluster(block_t *block) {
  dbg_assert(get_size(block) == cluster_size);
  dbg_assert(get_alloc(block));
  dbg_ensures(valid_block_format(block));

  // 需要在这个位置就压入链表
  // 设置Cluster Bit
  set_cluster((word_t *)block);

  // 清空Allocated field
  *cluster_alloc_field(block) = 0;

  uint8_t num = 0;
  // 设置每一个cluster block的第2个半字为对应编号
  for (word_t *p = get_cluster_block(block, 0); num != CLUSTER_BLOCK_COUNT;
       p += 2) {
    *p = pack_cluster_block_header(num);
    num++;
  }

  push_list(G_16, (list_elem_t *)get_body(block));
  set_front_alloc_of_back_block(block, true);
}
/**
 * @brief 利用CLUSTER_BLOCK的地址以及它的编号（NUM）推断出其所在Cluster的位置
 *
 * @param block
 * @param num
 * @return block_t*
 */
static inline block_t *get_cluster_by_cluster_block(void *cluster_block,
                                                    uint8_t num) {
  dbg_assert(check_word_align_word((word_t)cluster_block));
  dbg_assert(num < CLUSTER_BLOCK_COUNT);
  return (block_t *)(cluster_block - num * cluster_block_size - dsize);
}

/**
 * @brief 获取指定Cluster Block的标号
 *
 * @param cluster_block
 * @return uint8_t
 */
static inline uint8_t get_cluster_block_number(void *cluster_block) {
  uint8_t result = extract_cluster_block_num(*(word_t *)cluster_block);
  dbg_ensures(result < CLUSTER_BLOCK_COUNT);
  return result;
}

/**
 * @brief 获取Block中的第一个未使用的Cluster Block的编号
 *
 * @param block
 * @return uint8_t
 */
static uint8_t get_free_cluster_block(block_t *block) {
  word_t alloc_field = get_cluster_alloc_field(block);
  dbg_ensures(alloc_field < CLUSTER_ALLOC_STATUS);
  uint8_t num = cluster_alloc_to_num[alloc_field];
  dbg_ensures(num == CLUSTER_FULL ||
              get_cluster_block_alloc(block, num) == false);
  return num;
}

/**
 * @brief 在分配BLOCK中分配一个Cluster Block，将该Block的地址返回
 *
 * @param block
 * @param num
 * @return void* 如果Cluster中所有Cluster都已分配，返回NULL
 */
static void *allocate_cluster_block(block_t *block) {
  dbg_requires(block != NULL);
  dbg_assert(get_cluster(block) == true);
  dbg_assert(deduce_cluster_full(block) == false);

  uint8_t num = get_free_cluster_block(block);
  dbg_ensures(num != CLUSTER_FULL);

  // 直接就是第一个Byte
  uint8_t cluster_alloc_field = get_cluster_alloc_field(block);
  if (cluster_alloc_to_bit_count[cluster_alloc_field] ==
      CLUSTER_BLOCK_COUNT - 1) {
    // 分配此Block之后Cluster即满，需先将Block中G_16中移除
    pop_single((list_elem_t *)(list_table + G_16));
  }
  set_cluster_block_alloc(block, num, true);
  void *cluster_block = get_cluster_block(block, num);
  void *payload = cluster_block_to_payload(cluster_block);
  dbg_ensures(num != CLUSTER_FULL);
  dbg_ensures(get_cluster_block_number(cluster_block) == num);
  return payload;
}

/**
 * @brief 释放BLOCK中编号为NUM的Cluster Block
 *
 * @param block
 * @param num
 */
static void free_cluster_block(void *cluster_block) {
  dbg_requires(cluster_block != NULL);
  uint8_t num = get_cluster_block_number(cluster_block);
  dbg_ensures(num < CLUSTER_BLOCK_COUNT);
  block_t *cluster = get_cluster_by_cluster_block(cluster_block, num);
  dbg_ensures(valid_block_format(cluster));

  if (deduce_cluster_full(cluster)) {
    // 链表由满变非空，需要将其加入链表中
    set_cluster_block_alloc(cluster, num, false);
    push_list(G_16, (list_elem_t *)get_body(cluster));
  } else {
    set_cluster_block_alloc(cluster, num, false);
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
 * @brief 遍历堆中的所有block，直到CMP返回true为止
 *
 * @param block 目标BLOCK
 * @param cmp 接收两个block_t*，前者是BLOCK，后者是每次迭代时变更的block
 * @return block_t* cmp(block, curr)为true则返回curr，堆中无满足条件者返回NULL
 */
static block_t *find_heap_by_cmp(block_t *block,
                                 bool cmp(block_t *, block_t *)) {
  dbg_requires(block != NULL);
  dbg_requires(get_size(block) != 0);

  for (block_t *curr = HEAP_START; get_size(curr) != 0;
       curr = find_next(curr)) {
    if (cmp(block, curr) == true) {
      return curr;
    }
  }
  return NULL;
}

/**
 * @brief 遍历ROOT中的所有list_elem，直到CMP返回true为止
 *
 * @param root 待查找链表的起始Block
 * @param list_elem 用于比较的Block
 * @param cmp
 * 接收两个list_elem_t*，前者是LIST_ELEM，后者是每次迭代时变更的list_elem
 * @return list_elem_t*
 */
static list_elem_t *find_list_by_cmp(list_elem_t *root, list_elem_t *list_elem,
                                     bool cmp(list_elem_t *, list_elem_t *)) {
  dbg_requires(list_elem != NULL);
  dbg_requires(get_size(payload_to_header(list_elem)) != 0);

  for (list_elem_t *curr = root; curr != END_OF_LIST; curr = get_next(curr)) {
    if (cmp(list_elem, curr) == true) {
      return curr;
    }
  }
  return NULL;
}

/**
 * @brief Get the prev pointer of THIS
 *
 * @param this
 * @return list_elem_t*
 */
static inline list_elem_t *get_prev(list_elem_t *this) {
  dbg_assert(this != NULL);
  dbg_assert(check_is_node(payload_to_header(this)));
  return this->prev;
}

/**
 * @brief Set the prev pointer of THIS to LIST_ELEM
 *
 * @param this
 * @param block
 */
static inline void set_prev(list_elem_t *this, list_elem_t *block) {
  dbg_assert(this != NULL);
  dbg_assert(check_is_node(payload_to_header(this)));
  this->prev = block;
}

/**
 * @brief Get the next pointer of THIS
 *
 * @param this
 * @return list_elem_t*
 */
static inline list_elem_t *get_next(list_elem_t *this) {
  dbg_assert(check_is_node(payload_to_header(this)));
  return this->next;
}

/**
 * @brief Set the next pointer of THIS to LIST_ELEM
 *
 * @param this
 * @param block
 */
static inline void set_next(list_elem_t *this, list_elem_t *block) {
  dbg_assert(check_is_node(payload_to_header(this)));
  this->next = block;
}

/**
 * @brief 将CURR插入到FRONT之后
 *
 * @note FRONT可以是链表虚拟头节点
 *
 * @param front list_elem_t，CURR会被插入到它之后
 * @param curr list_elem_t，不可位于任何链表中
 * @pre FRONT和CURR都不可以是已分配的块
 *      FRONT不可以是链表的最后一个元素
 */
static void insert_after(list_elem_t *front, list_elem_t *curr) {
  dbg_assert(front != NULL);
  // dbg_assert(get_size(payload_to_header(front)) != 0);
  // dbg_assert(get_alloc(payload_to_header(front)) == false);
  // dbg_assert(check_free_block_aux(payload_to_header(front)) == true);
  dbg_assert(curr != NULL);
  dbg_assert(get_size(payload_to_header(curr)) != 0);
  dbg_assert(get_cluster(payload_to_header(curr)) ||
             !get_alloc(payload_to_header(curr)));
  dbg_assert(valid_block_format(payload_to_header(curr)));

  set_next(curr, get_next(front)); // curr->next = front->next;
  set_prev(curr, front);           // curr->prev = front;
  set_next(front, curr);           // front->next = curr;

  /* 如果FRONT有next结点的话，那么需要让该结点的prev指向curr */
  if (get_next(curr) != END_OF_LIST) // if (curr->next != NULL)
    set_prev(get_next(curr), curr);  // curr->next->prev = curr;
}

/**
 * @brief 将CURR插入到BACK之前
 *
 * @note BACK可以是链表虚拟头节点指向的节点
 *
 * @param curr 不可位于任何链表中
 * @param back CURR会被插入到它之前
 * @pre CURR和BACK都不可以是已分配的块
 *      CURR不可以是虚拟头节点
 */
static void insert_before(list_elem_t *curr, list_elem_t *back) {
  dbg_assert(back != NULL);
  // dbg_assert(get_size(payload_to_header(back)) != 0);
  // dbg_assert(get_alloc(payload_to_header(back)) == false);
  // dbg_assert(check_free_block_aux(payload_to_header(back)) == true);
  dbg_assert(curr != NULL);
  dbg_assert(get_size(payload_to_header(curr)) != 0);
  dbg_assert(get_alloc(payload_to_header(curr)) == false);
  dbg_assert(valid_block_format(payload_to_header(curr)) == true);

  set_prev(curr, get_prev(back)); // curr->prev = back->prev;
  set_next(curr, back);           // curr->next = back;
  set_prev(back, curr);           // back->prev = curr;

  /* 对于BACK有prev结点的话，需要让该结点的next指向curr */
  set_next(get_prev(curr), curr); //   curr->prev->next = curr;
}

/**
 * @brief 将NEW_HEAD插入到ROOT所指向的链表的头部
 *
 * @note ROOT必须为链表虚拟根节点
 *
 * @param root 链表虚拟根节点
 * @param new_head 将要被插入到ROOT所指向的链表的元素
 * @pre NEW_HEAD不可以是已分配的块
 */
static inline void push_front(list_elem_t *root, list_elem_t *new_head) {
  dbg_assert(root != NULL);
  dbg_assert(check_address_in_heap((word_t)root) == false);

  insert_after(root, new_head);
}
/**
 * @brief
 * 根据LIST_ELEM的地址顺序，将其插入到ROOT所指向的地址升序排列链表的合适位置
 *
 * @par 有可能ROOT指向的list_elem地址就比LIST_ELEM要大
 *
 * @param root 链表的虚拟头节点，其中元素按照地址升序进行排列
 * @param list_elem
 */
static void push_order(list_elem_t *root, list_elem_t *list_elem) {
  dbg_assert(root != NULL);
  dbg_assert(list_elem != NULL);
  dbg_assert(get_size(payload_to_header(list_elem)) != 0);
  dbg_assert(get_alloc(payload_to_header(list_elem)) == false);
  dbg_assert(valid_block_format(payload_to_header(list_elem)) == true);

  list_elem_t *prev =
      find_list_by_cmp(root, list_elem, cmp_insert_after_list_elem);
  dbg_assert(prev != NULL);
  insert_after(prev, list_elem);
  dbg_ensures(mm_checkheap(__LINE__));
}

/**
 * @brief 将LIST_ELEM推入**单向链表**ROOT中，因此只会修改list_elem->next字段
 *
 * @param root
 * @param list_elem
 */
static void push_single(list_elem_t *root, list_elem_t *list_elem) {
  dbg_assert(root != NULL);
  dbg_assert(list_elem != NULL);
  dbg_assert(get_size(payload_to_header(list_elem)) != 0);
  dbg_assert(get_alloc(payload_to_header(list_elem)) == true);
  dbg_assert(valid_block_format(payload_to_header(list_elem)) == true);

  set_next(list_elem, get_next(root));
  set_next(root, list_elem);
}

/**
 * @brief 将单向链表ROOT的首个元素弹出
 *
 * @param root
 */
static list_elem_t *pop_single(list_elem_t *root) {
  dbg_assert(root != NULL);

  list_elem_t *old_head = get_next(root);
  if (old_head != END_OF_LIST)
    set_next(root, get_next(old_head));
  return old_head;
}

/**
 * @brief 将ROOT所指向的链表的第一个元素移出链表，并将其返回LIST_ELEM
 *
 * @note ROOT必须为链表虚拟根节点
 *
 * @param root 链表虚拟根节点
 * @return list_elem_t* 链表的原第一个元素
 * @pre ROOT不能为NULL
 */
static list_elem_t *pop_front(list_elem_t *root) {
  dbg_assert(root != NULL);
  dbg_assert(check_address_in_heap((word_t)root) == false);

  list_elem_t *old_head = root->next;
  remove_list_elem(old_head);
  return old_head;
}

/**
 * @brief 检查可否将LIST_ELEM从对应链表中移出
 *
 * @param list_elem
 * @return true
 * @return false
 */
static bool check_remove(list_elem_t *list_elem) {
  dbg_assert(list_elem != NULL);
  block_t *block = payload_to_header(list_elem);
  dbg_assert(get_size(block) != 0);
  // 直接就是第一个Byte
  if (get_cluster(block)) {
    // 如果是Cluster，只只剩一个空位或全空的时候才可将其移除
    dbg_ensures(cluster_alloc_to_bit_count[get_cluster_alloc_field(block)] ==
                    CLUSTER_BLOCK_COUNT - 1 ||
                deduce_cluster_empty(block));
  }
  dbg_ensures(check_free_block_aux(block));
  return true;
}

/**
 * @brief 将LIST_ELEM从链表中移出链表
 *
 * @note LIST_ELEM必须位于某个链表中，可以是头节点
 *
 * @param list_elem
 * @return list_elem_t*
 * @pre LIST_ELEM不能为prologue list_elem或者epilogue list_elem
 */
static void remove_list_elem(list_elem_t *list_elem) {
  dbg_assert(check_remove(list_elem));

  if (get_next(list_elem) != END_OF_LIST) {
    set_prev(get_next(list_elem), get_prev(list_elem));
  }
  set_next(get_prev(list_elem), get_next(list_elem));
}

/**
 * @brief 根据TABLE_INDEX，将LIST_ELEM放入合适的链表中
 *
 * @param table_index
 * @param list_elem
 */
static void push_list(uint8_t table_index, list_elem_t *list_elem) {
  dbg_assert(table_index < LIST_TABLE_SIZE);

  list_elem_t *root = get_list_by_index(table_index);
  push_func_t push_func = index_to_push_func[table_index];
  push_func(root, list_elem);
  list_no_empty[table_index] = true;
}

/**
 * @brief Get the list by index
 *
 * @param index
 * @return list_elem_t*
 */
static inline list_elem_t *get_list_by_index(uint8_t index) {
  return (list_elem_t *)(list_table + index);
}

/**
 * @brief 推断最适合大小为ASIZE的block存放的free list
 *
 * @param asize 目标大小
 * @return uint8_t 合适的table index
 */
static inline uint8_t deduce_list_index(size_t asize) {
  return asize > MAX_BLOCK_GROUP
             ? G_INF
             : asize_to_index[((uint8_t)(asize >> 4)) & group_mask];
}

/**
 * @brief 比较CURR的后一个邻接的block是不是BLOCK
 *
 * @param block
 * @param curr
 * @return true
 * @return false
 */
static inline bool cmp_back_is_block(block_t *block, block_t *curr) {
  return find_next(curr) == block;
}

/**
 * @brief 检查CURR的next指针是否大于LIST_ELEM
 *
 * @note 按照地址升序确定是否要在LIST_ELEM的后面插入CURR
 *
 * @par
 * 为了和这个大于号适配，因此本来应该使用NULL表示的语义使用了END_OF_LIST进行标识
 *      具体来说，本来如果CURR是链表的最后一个block的话，那么CURR的next指针应该是
 *      NULL，用来表示这个元素之后就没有元素了。现在人为确保该指针是END_OF_LIST
 *      就能在保留 > 的情况下实现相同的语义
 *
 * @param list_elem
 * @param curr
 * @return true
 * @return false
 */
static inline bool cmp_insert_after_list_elem(list_elem_t *list_elem,
                                              list_elem_t *curr) {
  dbg_assert(list_elem != NULL);
  dbg_assert(curr != NULL);
  dbg_assert(curr < list_elem);

  // 实际使用的时候遍历列表中的list_elem，找到第一个next比BLOCK大的CURR就行了
  return get_next(curr) > list_elem;
}

/**
 * @brief
 * 遍历list_table中的所有链表，对其中所有元素调用AUX函数，执行失败即跳出循环。
 * 同时还会检查链表中的空置节点是否和堆中的空置节点数量相同
 *
 * @param aux 辅助函数，接受一个block_t*类型的参数，返回一个bool表示操作是否成功
 * @param heap_count 堆中的节点数目
 */
static bool valid_list_iterate(bool aux(block_t *), size_t heap_count) {
  bool validation = false;
  size_t list_count = 0;
  for (int i = 0; i < LIST_TABLE_SIZE; i++) {
    for (list_elem_t *curr = list_table[i]; curr != END_OF_LIST;
         curr = get_next(curr)) {
      list_count++;
      // 检查链表大小是否适合
      validation = check_size_list(i, curr);
      if (!validation) {
        dbg_printf("\n=============\n%d: Node size(%ld) do not match with list "
                   "size(%d)\n=============\n",
                   __LINE__, get_size(payload_to_header(curr)),
                   index_to_asize[i]);
        goto done;
      }

      validation = aux(payload_to_header(curr));
      if (!validation) {
        dbg_printf("\n=============\n%d: Aux fail\n=============\n", __LINE__);
        goto done;
      }
    }
  }
  validation = list_count == heap_count;
  if (!validation) {
    dbg_printf("\n=============\n%d: List count(%ld) not match with Heap "
               "count(%ld)\n=============\n",
               __LINE__, list_count, heap_count);
    goto done;
  }
done:
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
  return (word & low_four_bit_mask) == (word_t)0;
}

/**
 * @brief 检查WORD是否对齐单字，即低四位是否有东西
 *
 * @param word
 * @return true
 * @return false
 */
static bool check_word_align_word(word_t word) {
  return (word & low_four_bit_mask) == (word_t)8;
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

  validation = check_word_align_dword((word_t)get_body(block));
  if (!validation) {
    dbg_printf("\n=============\n%d: payload not alignment\n", __LINE__);
    goto done;
  }

  // 检查footer是不是对齐16Byte
  validation = check_word_align_dword((word_t)header_to_footer(block));
  if (!validation) {
    dbg_printf("\n=============\n%d: block footer not align to 16 "
               "Byte\n",
               __LINE__);
    goto done;
  }
done:
  if (!validation) {
    print_block(block);
    dbg_printf("=============\n");
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
  return block->header == *header_to_footer(block);
}

/**
 * @brief 检查Cluster的大小是否为128 Byte
 *
 * @param block
 * @return true
 * @return false
 */
static bool check_cluster_size(block_t *block) {
  return get_size(block) == cluster_size;
}

/**
 * @brief 检查Cluster的Header和Footer的alloc bit和cluster bit是否匹配
 *
 * @param block
 * @return true
 * @return false
 */
static bool check_cluster_tag(block_t *block) {
  const static word_t low_four_bit_mask = 0x5;
  return (block->header & low_four_bit_mask) ==
         (*header_to_footer(block) & low_four_bit_mask);
}

/**
 * @brief 检查各Cluster Block编号是否正确
 *
 * @param block
 * @return true
 * @return false
 */
static bool check_cluster_block_num(block_t *block) {
  uint8_t i = 0;
  for (void *p = get_cluster_block(block, 0); i != CLUSTER_BLOCK_COUNT;
       p += cluster_block_size) {
    if (i != get_cluster_block_number(p)) {
      dbg_printf("i: %d, get_cluster_block_number(p): %d\n", i,
                 get_cluster_block_number(p));
      return false;
    }
    i++;
  }
  return true;
}

/**
 * @brief 检查Cluster中分配情况是否和alloc bit情况匹配
 *
 * @par 如果alloc为0，那么不该有任何Cluster Block已分配；
 *      如果alloc不为0
 *
 * @param block
 * @return true
 * @return false
 */
static bool check_cluster_alloc_bit(block_t *block) {
  if (!get_alloc(block)) {
    return deduce_cluster_empty(block);
  }
  return true;
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

  validation = check_block_size(block);
  if (!validation) {
    dbg_printf("\n=============\n%d: block smaller than "
               "min_block_size\n",
               __LINE__);
    goto done;
  }

  // 只检查Free block
  if (!get_alloc(block)) {
    validation = check_tags_match(block);
    if (!validation) {
      dbg_printf("\n=============\n%d: block header & footer not match\n",
                 __LINE__);
      goto done;
    }
  }

  if (get_cluster(block)) {
    validation = check_cluster_size(block);
    if (!validation) {
      dbg_printf(
          "\n=============\n%d: Cluster block size no equals with 128 Byte\n",
          __LINE__);
      goto done;
    }
    if (!get_alloc(block)) {
      validation = check_cluster_tag(block);
      if (!validation) {
        dbg_printf("\n=============\n%d: Cluster header & footer no match with "
                   "each other\n",
                   __LINE__);
        goto done;
      }
    }

    validation = check_cluster_block_num(block);
    if (!validation) {
      dbg_printf("\n=============\n%d: Cluster block number interrupted\n",
                 __LINE__);
      goto done;
    }

    validation = check_cluster_alloc_bit(block);
    if (!validation) {
      dbg_printf("\n=============\n%d: Cluster allocated state interrupted\n",
                 __LINE__);
      goto done;
    }
  }

  validation = valid_block_align(block);
  if (!validation) {
    dbg_printf("\n=============\n%d: block not align\n", __LINE__);
    goto done;
  }
done:
  if (!validation) {
    print_block(block);
    dbg_printf("=============\n");
  }
  return validation;
}

/**
 * @brief 检查自己的front bit是否和前一个Block的alloc bit相互匹配
 *
 * @param block
 * @return true
 * @return false
 */
static bool check_front_alloc_bit(block_t *block) {
  if (block == HEAP_START) {
    // 自己是堆中第一个数据块的话
    return get_front_alloc(block);
  } else {
    // 如果前一个Block已分配的话，由于Footer不合法，因此只能迭代获取
    block_t *front_block = find_heap_by_cmp(block, cmp_back_is_block);
    dbg_assert(front_block != NULL);
    bool front_block_alloc = get_alloc(front_block);
    bool result = flip(get_front_alloc(block) ^ front_block_alloc);
    if (!result) {
      print_block(front_block);
    }
    return result;
  }
}

/**
 * @brief 检查LIST_ELEM是不是一个虚拟根节点
 *
 * @param list_elem
 * @return true
 * @return false
 */
static bool check_addr_is_root(list_elem_t *list_elem) {
  dbg_assert(list_table[0] != NULL);

  if (flip(check_address_in_heap((word_t)list_elem)) == false) {
    return false;
  }
  for (int i = 0; i < LIST_TABLE_SIZE; i++) {
    if (get_list_by_index(i) == list_elem) {
      return true;
    }
  }
  return false;
}

/**
 * @brief
 * 检查自己的next字段指向的节点的prev是否指向自己，如果next为空直接返回true
 *
 * @param list_elem
 * @return true
 * @return false
 */
static bool check_match_with_front(list_elem_t *list_elem) {
  return get_next(list_elem) != END_OF_LIST
             ? list_elem == get_prev(get_next(list_elem))
             : true;
}

/**
 * @brief
 * 检查自己的prev字段指向的节点的next是否指向自己，如果prev为空直接返回true
 *
 * @param list_elem
 * @return true
 * @return false
 */
static bool check_match_with_back(list_elem_t *list_elem) {
  return list_elem == get_next(get_prev(list_elem));
}

/**
 * @brief 检查LIST_ELEM的prev是否合法的地址
 *
 * @param list_elem
 * @return true
 * @return false
 */
static bool check_node_prev(list_elem_t *list_elem) {
  block_t *block = payload_to_header(list_elem);

  return check_address_in_heap((word_t)get_prev(list_elem)) ||
         check_addr_is_root(get_prev(list_elem)) || get_cluster(block);
}

/**
 * @brief 检查LIST_ELEM的next是否合法的地址
 *
 * @param list_elem
 * @return true
 * @return false
 */
static bool check_node_next(list_elem_t *list_elem) {
  return (check_address_in_heap((word_t)get_next(list_elem)) ||
          get_next(list_elem) == END_OF_LIST);
}

/**
 * @brief 检查BLOCK的next的地址是不是比BLOCK的地址大
 *
 * @param list_elem
 * @return true
 * @return false
 */
static bool check_node_ordered_with_next(list_elem_t *list_elem) {
  return get_next(list_elem) == END_OF_LIST || get_next(list_elem) > list_elem;
}

/**
 * @brief 检查LIST_ELEM是否位于INDEX所指示的链表中
 *
 * @param index
 * @param list_elem
 * @return true
 * @return false
 */
static bool check_size_list(uint8_t index, list_elem_t *list_elem) {
  dbg_ensures(index < LIST_TABLE_SIZE);
  block_t *block = payload_to_header(list_elem);

  switch (index) {
  case G_16:
    return get_size(block) == index_to_asize[index];
    break;
  case G_32:
  case G_48:
  case G_64:
    return get_size(block) == index_to_asize[index];
    break;
  case G_128:
  case G_192:
  case G_256:
  case G_384:
  case G_512:
  case G_1024:
  case G_2048:
  case G_1536:
  case G_4096:
    return get_size(block) <= index_to_asize[index] &&
           get_size(block) > index_to_asize[index - 1];
  case G_INF:
    return get_size(block) > index_to_asize[index - 1];
  default:
    return false;
  }
}

/**
 * @brief 检查指定BLOCK的格式是否与链表结点的语法对应
 *
 * @return true
 * @return false
 */
static bool check_is_node(block_t *block) {
  return check_addr_is_root(get_body(block)) || !get_alloc(block) ||
         (get_cluster(block) && !deduce_cluster_full(block));
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
  list_elem_t *list_elem = (list_elem_t *)get_body(block);
  dbg_assert(!get_alloc(block) ||
             (get_cluster(block) && !deduce_cluster_full(block)));

  // 检查next以及prev指针
  validation = check_node_next(list_elem);
  if (!validation) {
    dbg_printf("\n=============\n%d: next invalid (%p)", __LINE__,
               get_next(list_elem));
    goto done;
  }

  validation = check_node_prev(list_elem);
  if (!validation) {
    dbg_printf("\n=============\n%d: prev invalid (%p)", __LINE__,
               get_prev(list_elem));
    goto done;
  }

  validation = get_cluster(block) || check_match_with_front(list_elem);
  if (!validation) {
    dbg_printf("\n=============\n%d: next list_elem's prev don't point to this "
               "list_elem\n",
               __LINE__);
    goto done;
  }

  validation = get_cluster(block) || check_match_with_back(list_elem);
  if (!validation) {
    dbg_printf("\n=============\n%d: prev list_elem's next don't point to this "
               "list_elem\n",
               __LINE__);
    goto done;
  }

  // if (get_size(block) > MAX_SINGLE_BLOCK_GROUP && !get_cluster(block)) {
  //   validation = check_node_ordered_with_next(list_elem);
  //   if (!validation) {
  //     dbg_printf("\n=============\n%d: Address of next pointer(%p) higher
  //     than "
  //                "this list_elem(%p)"
  //                "\n",
  //                __LINE__, get_next(list_elem), list_elem);

  //     goto done;
  //   }
  // }

done:
  if (!validation) {
    print_block(block);
    dbg_printf("=============\n");
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
static bool check_free_block_aux(block_t *block) {
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
  block_t *result = block;
  block_t *adj_back = find_next(block);
  list_elem_t *adj_back_list_elem = (list_elem_t *)get_body(adj_back);
  bool adj_front_allocated = get_front_alloc(block);
  bool adj_back_allocated = get_alloc(adj_back);

  // 由于无两连续Free block的不变性始终会被保证，因此front的front必然已分配
  if (adj_front_allocated) {
    if (adj_back_allocated) {
      // Case 1 两边都已分配
    } else {
      // Case 2 后边已释放 上述两种情况都不需要改变result
      remove_list_elem(adj_back_list_elem);
      write_block(block, get_size(block) + get_size(adj_back), false, true);
    }
  } else {
    block_t *adj_front = find_prev(block);
    list_elem_t *adj_front_list_elem = (list_elem_t *)get_body(adj_front);
    if (adj_back_allocated) {
      // Case 3 前边已释放
      remove_list_elem(adj_front_list_elem);
      write_block(adj_front, get_size(adj_front) + get_size(block), false,
                  true);
      result = adj_front;
    } else {
      // Case 4 两边都已释放
      remove_list_elem(adj_front_list_elem);
      remove_list_elem(adj_back_list_elem);
      write_block(adj_front,
                  get_size(adj_front) + get_size(block) + get_size(adj_back),
                  false, true);
      result = adj_front;
    }
  }
  set_front_alloc_of_back_block(result, false);
  return result;
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

  // 首先需要将epilogue block的front_alloc_bit保存起来
  word_t old_epilogue = *(word_t *)(bp - wsize);
  bool front_alloc_bit = extract_front_alloc(old_epilogue);

  // Initialize free block header/footer
  block_t *block = payload_to_header(bp);
  write_block(block, size, false, front_alloc_bit);

  // Create new epilogue header 需要先把epilguos写入
  block_t *block_next = find_next(block);
  write_epilogue(block_next, false);

  // Coalesce in case the previous block was free
  block = coalesce_block(block);

  // 更新链表头部为新Free Block
  push_list(deduce_list_index(get_size(block)), (list_elem_t *)get_body(block));

  dbg_ensures(valid_node(block));
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
 * @pre block必须已分配
 */
static void split_block(block_t *block, size_t asize) {
  dbg_requires(get_alloc(block));
  dbg_requires(asize <= get_size(block));
  dbg_requires(check_word_align_dword((word_t)asize));
  /* TODO: Can you write a precondition about the value of asize? */

  size_t block_size = get_size(block);

  // BLOCK的后一个Block来说最后的front bit应该是？
  bool result_front_bit = true;
  block_t *result_last_block = block;

  if ((block_size - asize) >= min_block_size) {
    block_t *block_next;
    write_block(block, asize, true, get_front_alloc(block));

    block_next = find_next(block);
    // 如果切分了Block，那么它之前的Block应该是未分配状态
    write_block(block_next, block_size - asize, false, true);
    // 将新的Free Block插入到合适的List中
    push_list(deduce_list_index(block_size - asize),
              (list_elem_t *)get_body(block_next));
    // 它的前一个Block现在是free状态了
    result_front_bit = false;
    result_last_block = block_next;

    // LIFO验证 dbg_ensures(block_next == free_list_root);
  }
  set_front_alloc_of_back_block(result_last_block, result_front_bit);

  dbg_ensures(mm_checkheap(__LINE__));
  dbg_ensures(get_alloc(block));
}

/**
 * @brief 遍历INDEX对应的链表，寻找大小等于ASIZE或大于等于ASIZE + 32的块
 *
 * @par 扫描算法分为两个部分：
 * 1. 第一部分是在index对应链表中进行扫描，利用Best Fit算法，过程中
 *    如果遇到大小恰好为ASIZE的Block会立刻返回，如果遇到大于等于ssize
 *    的块则会将其记录。
 *
 *    如果一直到队列末尾都没有遇到大小相等的Block，同时有记录到ssize块的话
 *    那么会将该块返回，否则进入下一部分；
 *
 * 2. 第二部分的流程为First fit，需要使用ssize获取新的list table index，
 *    找到对应链表中第一个大于或等于ASIZE的Block并将其返回；
 *
 * 这一算法可有效减少内存的Internal Fragmentation现象
 *
 * @param[in] asize 目标大小
 * @param[in] index list_table下标
 * @return 块的地址，如果没有找到则是NULL
 */
static block_t *find_good_fit(size_t asize, uint8_t index) {
  dbg_assert(asize >= 32);

  list_elem_t *list_elem;
  block_t *block = NULL;
  size_t ssize = asize + min_block_size;
  // 保存满足条件( >= ssize )的Block
  block_t *sblock = NULL;

  if (list_no_empty[index] == false) {
    goto section2;
  }

  list_elem = get_next(get_list_by_index(index));
  if (list_elem == END_OF_LIST) {
    list_no_empty[index] = true;
    goto section2;
  }

  do {
    block = payload_to_header(list_elem);
    if (asize == get_size(block)) {
      return block;
    } else if (sblock == NULL && ssize <= get_size(block)) {
      sblock = block;
    }
    list_elem = get_next(list_elem);
  } while (list_elem != END_OF_LIST);

  if (sblock != NULL) {
    return sblock;
  }
section2:
  index = deduce_list_index(ssize);
  for (int i = index; i != LIST_TABLE_SIZE; i++) {
    // 如果链表是空的直接跳过
    if (list_no_empty[i] == false) {
      continue;
    }

    // 由于再清理链表元素的时候不会更新对应链表空状态，因此这里需要检查一下
    list_elem = get_next(get_list_by_index(i));
    if (list_elem == END_OF_LIST) {
      // 如果没有更新空状态，那么需要显式更新一下
      list_no_empty[i] = true;
      continue;
    }

    do {
      block = payload_to_header(list_elem);
      // 优化掉了 get_alloc(block) 先比较是不是小于 get_size(block) + block size
      if (ssize <= get_size(block)) {
        return block;
      }
      list_elem = get_next(list_elem);
    } while (list_elem != END_OF_LIST);
  }
  return NULL; // no fit found
}

/**
 * @brief 找到第一个大于或等于ASIZE的Block，没有找到就切换到下一个链表
 *
 * TODO 这里也需要加上一段，中间用来检查ASIZE是不是32或者48，如果是的话++index
 *
 * @param asize 目标大小
 * @param index list_table下标
 * @return block_t*
 */
static block_t *find_first_fit(size_t asize, uint8_t index) {
  list_elem_t *list_elem;
  block_t *block = NULL;
  // 如果链表是空的直接跳过
  if (list_no_empty[index] == false) {
    goto section2;
  }

  // 由于再清理链表元素的时候不会更新对应链表空状态，因此这里需要检查一下
  list_elem = get_next(get_list_by_index(index));
  if (list_elem == END_OF_LIST) {
    // 如果没有更新空状态，那么需要显式更新一下
    list_no_empty[index] = true;
    goto section2;
  }

  do {
    block = payload_to_header(list_elem);
    if (asize <= get_size(block)) {
      return block;
    }
    list_elem = get_next(list_elem);
  } while (list_elem != END_OF_LIST);
  if (asize == 32 || asize == 48) {
    index++;
  }
section2:
  for (int i = index; i < LIST_TABLE_SIZE; i++) {
    // 如果链表是空的直接跳过
    if (list_no_empty[i] == false) {
      continue;
    }

    // 由于再清理链表元素的时候不会更新对应链表空状态，因此这里需要检查一下
    list_elem = get_next(get_list_by_index(i));
    if (list_elem == END_OF_LIST) {
      // 如果没有更新空状态，那么需要显式更新一下
      list_no_empty[i] = true;
      continue;
    }

    do {
      block = payload_to_header(list_elem);
      if (asize <= get_size(block)) {
        return block;
      }
      list_elem = get_next(list_elem);
    } while (list_elem != END_OF_LIST);
  }
  return NULL; // no fit found
}

/**
 * @brief 根据ASIZE选择调用合适的fit函数
 *
 * @param asize
 * @return block_t*
 */
static inline block_t *find_fit(size_t asize) {
  uint8_t index = deduce_list_index(asize);
  block_t *result = index_to_fit_func[index](asize, index);
  return result;
}

/**
 * @brief 获取一个Cluster，如果没有则返回NULL
 *
 * @return block_t*
 */
static block_t *find_cluster_fit() {
  list_elem_t *list_elem;
  if (list_no_empty[G_16] == false) {
    return NULL;
  }

  list_elem = get_next(get_list_by_index(G_16));
  if (list_elem == END_OF_LIST) {
    list_no_empty[G_16] = true;
    return NULL;
  }
  // 非空的话返回第一个就好了
  return payload_to_header(list_elem);
}

/**
 * @brief 遍历ROOT所指代的链表，找到其中list_elem
 * size最接近且大于ASZIE的block_t为止
 *
 * @warning 需改为递增查找
 *
 * @param asize 目标list_elem的大小
 * @param root 链表根节点
 * @return block_t* 如果没有找到返回NULL
 */
static block_t *find_best_fit(size_t asize, list_elem_t *root) {
  list_elem_t *list_elem;
  block_t *block = NULL;
  block_t *min_block = NULL;
  for (list_elem = root; list_elem != END_OF_LIST;
       list_elem = get_next(list_elem)) {
    block = payload_to_header(list_elem);
    if (!(get_alloc(block)) && (asize <= get_size(block))) {
      if (min_block == NULL || get_size(min_block) > get_size(block)) {
        min_block = block;
      }
    }
  }
  return min_block; // no fit found
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
  block_t *curr = NULL;

  // 检查全局数组大小是否和LIST_TABLE_SIZE匹配
  valid = (sizeof(index_to_push_func) / sizeof(index_to_push_func[0])) ==
          LIST_TABLE_SIZE;
  if (!valid) {
    dbg_printf("\n=============\n%d: index_to_push_func size no equals to "
               "LIST_TABLE_SIZE",
               __LINE__);
    goto done;
  }
  valid = (sizeof(list_table) / sizeof(list_table[0])) == LIST_TABLE_SIZE;
  if (!valid) {
    dbg_printf(
        "\n=============\n%d: list_table size no equals to LIST_TABLE_SIZE",
        __LINE__);
    goto done;
  }
  valid = (sizeof(index_to_push_func) / sizeof(index_to_push_func[0])) ==
          LIST_TABLE_SIZE;
  if (!valid) {
    dbg_printf("\n=============\n%d: index_to_push_func size no equals to "
               "LIST_TABLE_SIZE",
               __LINE__);
    goto done;
  }
  valid = (sizeof(cluster_alloc_to_num) / sizeof(cluster_alloc_to_num[0])) ==
          CLUSTER_ALLOC_STATUS;
  if (!valid) {
    dbg_printf("\n=============\n%d: cluster_alloc_to_num size no equals to "
               "CLUSTER_ALLOC_STATUS",
               __LINE__);
    goto done;
  }
  valid = (sizeof(cluster_alloc_to_num) / sizeof(cluster_alloc_to_num[0])) ==
          CLUSTER_ALLOC_STATUS;
  if (!valid) {
    dbg_printf("\n=============\n%d: cluster_alloc_to_num size no equals to "
               "CLUSTER_ALLOC_STATUS",
               __LINE__);
    goto done;
  }

  // 检查prologue block格式
  valid = check_tag(*find_prev_footer(HEAP_START), 0, true);
  if (!valid) {
    dbg_printf("\n=============\n%d: prologue block format error!", __LINE__);
    goto done;
  }

  // 检查free list中所有的block

  size_t count = 0;

  // 检查堆中的每一个块的格式是否合法，同时统计其中free block的数目
  for (curr = HEAP_START; get_size(curr) != 0; curr = find_next(curr)) {
    valid = valid_block_format(curr);
    if (!valid) {
      dbg_printf("\n=============\n%d: Block format invalid", __LINE__);
      goto done;
    }
    valid = check_front_alloc_bit(curr);
    if (!valid) {
      dbg_printf("\n=============\n%d: Block alloc bit not match with front "
                 "block",
                 __LINE__);
      goto done;
    }

    if (get_cluster(curr)) {
      if (!deduce_cluster_full(curr)) {
        count++;
      }
    } else {
      if (!get_alloc(curr)) {
        count++;
      }
    }
  }

  // 检查epilogue block是否合法
  valid = check_tag(curr->header, 0, true);
  if (!valid) {
    dbg_printf("\n=============\n%d: epilogue Block invalid", __LINE__);
    goto done;
  }

  // 遍历链表中的所有节点，检查它们是否合法
  valid = valid_list_iterate(valid_node, count);
  if (!valid) {
    dbg_printf("\n=============\n%d: List invalid", __LINE__);
    goto done;
  }
done:
  if (!valid) {
    if (curr != NULL) {
      print_block(curr);
    }
    dbg_printf("\n=============\n");
  }

  return valid;
}

/**
 * @brief 初始化堆
 *
 * @par 初始状况下的堆长度为64Byte (4 DWord) + chunksize：
 * - DWord1：prologue block的footer；
 * - DWord2：epilogue block的header；
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

  start[0] = pack_regular(0, true, true); // Heap prologue (block footer)
  start[1] = pack_regular(0, true, true); // Heap epilogue (block header)

  // 将各segregate list指针从NULL显式初始化为END_OF_LIST
  for (int i = 0; i != LIST_TABLE_SIZE; i++)
    list_table[i] = END_OF_LIST;

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
  if (list_table[0] == NULL) {
    mm_init();
  }

  // Ignore spurious request
  if (size == 0) {
    dbg_ensures(mm_checkheap(__LINE__));
    return bp;
  }

  // 用于表示要不要执行和Cluster Block分配相关的逻辑
  bool alloc_cluster = size < dsize;
  // Cluster Block & Regular Block
  if (alloc_cluster) {
    // 查看系统中有没有现成的Cluster
    block = find_cluster_fit();
    if (block != NULL) {
      goto alloc_cluster;
    }
    // 否则，需要构造一个新的Cluster
    asize = cluster_size;
  } else {
    // Adjust block size to include overhead and to meet alignment requirements
    asize = round_up(size + overhead_size, dsize);
    // 由于使用Round
    // up可以确保至少为min_block_size，因此无需执行max(min_block_size, asize)
  }
  // 需要放外边 Search the free list for a fit
  // block = find_good_fit(asize, deduce_list_index(asize));
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
  // Mark block as allocated
  remove_list_elem(get_body(block));
  size_t block_size = get_size(block);
  write_block(block, block_size, true, get_front_alloc(block));
  // Try to split the block if too large
  split_block(block, asize);

  if (alloc_cluster) {
    // 如果是通过判断语句到达这里的，代表需要在128Byte Block上创建Cluster
    create_cluster(block);
  alloc_cluster:
    // 如果是通过goto到达这里的，代表找到了一个已有的Cluster
    dbg_assert(!deduce_cluster_full(block));
    bp = allocate_cluster_block(block);
    dbg_assert(!deduce_cluster_empty(block));
    dbg_ensures(valid_block_format(block));
  } else {
    bp = header_to_payload(block);
  }
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
  if (get_cluster(block)) {
    free_cluster_block((void *)block);
  } else {
    size_t size = get_size(block);

    // The block should be marked as allocated
    dbg_assert(get_alloc(block));

    // Mark the block as free
    write_block(block, size, false, get_front_alloc(block));
    set_front_alloc_of_back_block(block, false);

    // Try to coalesce the block with its neighbors
    block = coalesce_block(block);

    // 将新Free block插入到合适的链表中
    push_list(deduce_list_index(get_size(block)),
              (list_elem_t *)get_body(block));
  }

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
  copysize = get_body_size(block); // gets size of old payload
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