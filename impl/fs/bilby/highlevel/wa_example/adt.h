#ifndef ADT_H__
#define ADT_H__

#include <stdlib.h>
#include <string.h>

#define kmalloc(size) malloc(size)
#define kzalloc(size) calloc(size, sizeof (char))
#define kfree(obj) free(obj)

struct semaphore {
  int dummy;
};

#endif /* ADT_H__ */
