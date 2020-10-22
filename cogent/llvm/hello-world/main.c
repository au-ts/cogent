#include <stdio.h>

typedef void *SysState;

#include "hello_world.h"

print_string_ret print_string(print_string_arg arg)
{
    printf("%s\n", arg.p2);
    return arg.p1;
}

int main(void)
{
    SysState st;
    st = helloworld(st);
    return 0;
}
