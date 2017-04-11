#include <stdio.h>
#include <stdlib.h>
#include "foo.h"

void *my_malloc(size_t s);
void my_free(void *p);
void my_lock_acquire();
void my_lock_release();
void my_fork(void(*foo)());

// What about a program that does something racy on the stack? Storing a stack address
// in a global variable on the heap or something?

long long baz(void)
{
    long long x = 3;
    return x;
}

/**
 * XXX {P} {}
 */
int foo(void)
{
    int *x = my_malloc(sizeof(int));
    struct blah q = { .z = 4, .w = 9 };
    *x = bar(&q);
    my_free(x);
    return baz();
}
