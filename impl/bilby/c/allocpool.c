/*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 */

#include "bilbyfs.h"

struct kmem_cache *bilbyfs_node_slab;

static inline void node_slab_ctor(void *node)
{
        memset(node, 0, NODE_SIZE);
}

int allocpool_init(struct alloc_pool *pool)
{
        bilbyfs_node_slab = kmem_cache_create("bilbyfs_node_slab",
                                NODE_SIZE, 0,
                                SLAB_MEM_SPREAD | SLAB_RECLAIM_ACCOUNT,
                                &node_slab_ctor);
        if (!bilbyfs_node_slab)
                return -ENOMEM;
        pool->len = 0;
        pool->arr = NULL;
        return 0;
}

void allocpool_destroy(struct alloc_pool *pool)
{
         kmem_cache_destroy(bilbyfs_node_slab);
         kfree(pool->arr);
         pool->arr = NULL;
}

int allocpool_alloc(struct alloc_pool *pool, int sz_pool, int sz_obj)
{
        int i;
        if (pool->len < sz_pool) {
                pool->sz_obj = sz_obj;
                pool->len  = sz_pool;
                pool->arr = krealloc(pool->arr, sizeof(void *) * sz_pool);
        }
        if (pool->arr) {
                memset(pool->arr, 0, sizeof(void *) * pool->len);
                pool->i = 0;
                for (i = 0; i < pool->len; i++) {
                        pool->arr[i] = kmem_cache_alloc(bilbyfs_node_slab, GFP_NOFS);
                        if (!pool->arr[i]) {
                                allocpool_empty(pool);
                                return -ENOMEM;
                        }
                }
                return 0;
        }
        return -ENOMEM;
}

void allocpool_free_single(void *p)
{
        kmem_cache_free(bilbyfs_node_slab, p);
}

void allocpool_empty(struct alloc_pool *pool)
{
        int i;

        for (i = 0; i < pool->len; i++) {
                if (pool->arr[i])
                        kmem_cache_free(bilbyfs_node_slab, pool->arr[i]);
                pool->arr[i] = NULL;
        }
        pool->i = 0;
}

void *allocpool_pop(struct alloc_pool *pool)
{
        void *p;
        int err;
        /* struct timeval st, stp; */


        pool->tot_nodes_needed += 1;
        if (pool->i >= pool->len) {
                /* do_gettimeofday(&st); */
                err = allocpool_alloc(pool, pool->len, pool->sz_obj);
                /* do_gettimeofday(&stp);
                pr_err("timed allocpool_alloc() in pop : %ld sec %ld usec\n", stp.tv_sec - st.tv_sec, stp. tv_usec - st.tv_usec); */
                bilbyfs_assert(!err);
        }
        p = pool->arr[pool->i];
        if (p) {
                pool->arr[pool->i] = NULL;
                pool->i += 1;
                return p;
        }
        /* This should never happen */
        bilbyfs_assert(false);
        return NULL;
}

