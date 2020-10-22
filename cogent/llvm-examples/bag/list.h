#include <cogent-llvm-defns.h>

struct List_u32
{
    struct List_u32 *next;
    u32 data;
};

typedef struct List_u32 List_u32;
