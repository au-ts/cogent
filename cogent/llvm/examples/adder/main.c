#include <stdio.h>
#include <stdlib.h>

#include "adder.h"

int main(void)
{
    u32 first_num = 19;
    u32 second_num = 2;

    add_ret ret = add((add_arg){first_num, second_num});
    if (ret.tag == Success)
    {
        u32 sum = ret.val.Success;
        printf("Sum is %u\n", sum);
        return 0;
    }
    else
    {
        printf("Error: Overflow detected.\n");
        return 1;
    }
}
