#include "foo.h"

int x = 4;

int bar(struct blah *q) {
    if (q->z == 3) {
    	*(int *)(q + q->w) = q->w;
    }
    return q->z + x;
}
