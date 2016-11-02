/*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 */

#include <plat/linux/wrapper_pp_inferred.c>

static int __init init_skel_fs(void)
{
        return 0;
}


static void __exit exit_skel_fs(void)
{
}


module_init(init_skel_fs)
module_exit(exit_skel_fs)

MODULE_AUTHOR("Data61 TFS Team");
MODULE_DESCRIPTION("Sekeleton FS implementation in Cogent");
MODULE_LICENSE("GPL");
