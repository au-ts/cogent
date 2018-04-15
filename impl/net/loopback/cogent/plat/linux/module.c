/*
 * Copyright 2018, Data61
 * Commonwealth Scientific and Industrial Research Organisation (CSIRO)
 * ABN 41 687 119 230.
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(DATA61_GPL)
 */

#include <plat/linux/wrapper_pp_inferred.c>

static unsigned int cg_loopback_net_id __read_mostly;

struct cg_loopback_net {
        int loopback;
};

static __net_init int cg_loopback_net_init(struct net *net)
{
        return cg_loopback_net_init_ac(net);
}

static __net_exit void cg_loopback_net_exit(struct net *net)
{
}

static struct pernet_operations cg_loopback_net_ops = {
        .init = cg_loopback_net_init,
        .exit = cg_loopback_net_exit,
        .id   = &cg_loopback_net_id,
        .size = sizeof(struct cg_loopback_net),
};

static int __init cg_loopback_init(void)
{
        int err;

        err = register_pernet_device(&cg_loopback_net_ops);
        if (err)
                goto out;

        return 0;
out:
        return err;
}

static void cg_loopback_exit(void)
{
        unregister_pernet_device(&cg_loopback_net_ops);
}

module_init(cg_loopback_init)
module_exit(cg_loopback_exit)

MODULE_AUTHOR("Data61 Team");
MODULE_DESCRIPTION("Network loopback interface implementation in Cogent");
MODULE_LICENSE("GPL");

