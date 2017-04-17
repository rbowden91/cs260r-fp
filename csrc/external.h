#ifndef EXTERNAL_H
#define EXTERNAL_H

#include <stdlib.h>

struct my_lock;

struct my_lock *my_lock_create(void);
void my_lock_acquire(struct my_lock *lk);
void my_lock_release(struct my_lock *lk);
void my_lock_destroy(struct my_lock *lk);

void *my_malloc(size_t s);
void my_free(void *p);

void my_fork(void(*foo)());

#endif /* EXTERNAL_H */
