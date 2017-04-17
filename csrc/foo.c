#include "foo.h"
#include "external.h"

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
