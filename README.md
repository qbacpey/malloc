# malloc  

This is the malloc lab for CMU 15-213. Students are required to optimize the initial Implicit List malloc implementation provided at the beginning of the course, using the memory allocation policies covered in class. The final implementation generally includes the following features:  

- **Placement policy**: Best fit  
- **List**: Segregated List  
- **Splitting policy**: Minimum size for splitting  
- **Coalescing policy**: Immediate coalescing  
- **Insertion policy**: LIFO & address order  
- **Eliminating footers**: Yes  

---

## Segregated List  

Due to the project constraint of a maximum total global variable size of 128 bytes, only 14 segregated lists are maintained.  

Based on the size of chunks they can store, these lists can be divided into three categories:  

---

### Minimum Block Cluster List  

`malloc` allocates free blocks of size 16 bytes in "clusters":  

- Each cluster is **128 bytes in size**:  
  - The overall structure of a cluster is similar to a regular free block, including a header and footer.  
  - The **allocated bit** in the cluster header is set to `1` only after all free blocks within the cluster are allocated.  
  - The fifth byte of the cluster header tracks the allocation status of internal free blocks, from the least significant bit to the sixth bit.  
  - Following the cluster header is a `list_elem_t` structure, linking all clusters (allocated or not) together.  
- Each cluster contains six **mini-blocks** of 15 bytes each:  
  - When `free` is called, it checks the preceding byte of the block's address to determine whether the block is part of a cluster. If it is, the block's position within the cluster is calculated to locate the cluster header.  
  - The remaining 32 bytes of the 128-byte cluster are used for cluster maintenance overhead.  
- The cluster list is maintained in **LIFO order**: if any mini-block in a cluster is freed, the cluster is moved to the head of the list.  

---

### Small List  

There are three small lists, each dedicated to free blocks of size **32 bytes, 48 bytes, and 64 bytes**.  

These lists are maintained similarly to the **Small Bin** in `glibc`:  
- Free blocks are managed using a **doubly linked list**.  
- Each list can only contain free blocks of a single size.  
- Free blocks can be inserted in **LIFO order** or based on **address order**.  

---

### Large List  

There are nine large lists, each covering a specific range of free block sizes, such as **64, 128, 256... 4096 bytes**.  

These lists are maintained similarly to the **Large Bin** in `glibc`:  
- Free blocks are managed using a **doubly linked list**.  
- Each list can only contain free blocks within its designated size range.  
- Free blocks can be inserted in **LIFO order** or based on **address order**.  

If a requested free block exceeds 4096 bytes, it is placed in a segregated list with no upper size limit.  
