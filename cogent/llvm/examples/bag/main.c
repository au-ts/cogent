#include <stdio.h>
#include <stdlib.h>

typedef void *Heap;

#include "list.h"
#include "bag.h"

newBag_ret newBag(newBag_arg heap)
{
    Bag *bag = malloc(sizeof(*bag));
    if (!bag)
        return (newBag_ret){Failure, .val.Failure = heap};

    bag->count = 0;
    bag->sum = 0;

    return (newBag_ret){Success, .val.Success = {bag, heap}};
}

freeBag_ret freeBag(freeBag_arg args)
{
    free(args.p2);
    return args.p1;
}

reduce_0_ret reduce_0(reduce_0_arg args)
{
    List_u32 *list = args.p1;
    t1 *acc = args.p3;

    t2 fargs;
    while (list)
    {
        fargs.p1 = list->data;
        fargs.p2 = acc;
        acc = (args.p2)(fargs);
        list = list->next;
    }

    return acc;
}

int main()
{
    List_u32 *list = NULL;

    u32 x = 0;
    while (1)
    {
        printf("Enter a number: ");
        if (scanf("%d", &x) < 0)
            break;

        List_u32 *cell = malloc(sizeof(*cell));
        cell->data = x;
        cell->next = list;
        list = cell;
    }

    List_u32 *curr;
    curr = list;

    printf("\nThe list is: ");
    while (curr != NULL)
    {
        printf("%d -> ", curr->data);
        curr = curr->next;
    }
    printf("NULL\n");

    average_ret avg_ret = average((average_arg){NULL, list});
    printf("The average is: %d\n", avg_ret.p2);

    return 0;
}
