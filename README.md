# malloc

这是CMU 15-213的malloc lab。学生需要利用课程所学的内存分配政策，对课程初始给定的Implicit List malloc实现做出优化。本项目的最终实现情况大致如下：
+ Placement policy：Best fit
+ List：Segregate List
+ Splitting policy：不少于最小块的大小即可
+ Coalescing policy：Immediate coalesce
+ Insertion policy：LIFO & Address order
+ Eliminating Footers：Yes

## Segregate List

由于本项目限制只能使用总大小为128 Byte全局变量，因此本项目只维护了14个Segregate List

按照其中可保存的Chunk的大小，可以将它们分为三类

### Minimum Block Cluster List

`malloc`会以“集群”方式分配大小为16 Byte的Free Block：

+ 每一个集群大小为128 Byte：
  + 集群的整体结构和普通Free Block一样，都拥有头部（Header）和尾部（Footer）；
  + 只有在集群内部所有Free Block都被分配过后，集群头部的Allocated Bit才被标记为1，表示此集群分配完全；
  + 集群头部第五个Byte用于表示集群Block内部Free Block的分配情况，从最底位开始，一直到第六位；
  + 集群头部的后面是一个`list_elem_t`结构体，系统所有集群（无论是否分配完全）都通过此结构体串联起来；
+ 一个集群可容纳6个可用空间为15 Byte的Mini Block：
  + `free`被调用时会检查当前Block所在地址的前一个Byte，确认当前Block是不是某一个集群内部的Mini  Block，如果是，那么需要计算当前Mini Block在整个集群中的编号，进而获取集群头部的所在位置；
  + 128 Byte中其余的32 Byte是维护集群所必需的空间开销；
+ 集群链表采用LIFO方式进行维护，一旦释放了集群中的任意一个Mini Block，都需要将集群推入链表头部；

### Small List

共有三条，各自分别用于容纳大小为`32 Byte, 48 Byte, 64 Byte`的Free Block

维护方式与结构类似于`glibc`中的Small Bin：
+ 采用双向链表维护Free Block；
+ 每条List中只能有一种大小的Free Block；
+ 支持LIFO，也支持以地址顺序插入Free Block；

### Large List

共有九条，各自分别用于容纳一定范围的Free Block，`64, 128, 256 ... 4096`每一段对应一个List

维护方式与结构类似于`glibc`中的Large Bin：
+ 采用双向链表维护Free Block；
+ 每条List中只能有给定范围大小的Free Block；
+ 支持LIFO，也支持以地址顺序插入Free Block；

如果请求的Free Block大于4096，将其归入可容纳大小无上限的Segregate List
