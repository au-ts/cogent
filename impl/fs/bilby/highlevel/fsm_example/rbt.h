/*
 * @TAG(OTHER_GPL)
 */

/*
Modified from the following two files:

<linux-kernel>/Documentataion/rbtree.txt

Red-black Trees (rbtree) in Linux
January 18, 2007
Rob Landley <rob@landley.net>

=============================

Red Black Trees
(C) 1999 Andrea Arcangeli <andrea@suse.de>

This program is free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 2 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program; if not, write to th
e Free Software
  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA

  linux/include/linux/rbtree.h

  To use rbtrees you'll have to implement your own insert and search cores.
  This will avoid us to use callbacks and to drop drammatically performances.
  I know it's not the cleaner way,  but in C (not in C++) to get
  performances and genericity...

  See Documentation/rbtree.txt for documentation and samples.
*/


#ifndef LIB_RBT_H__
#define LIB_RBT_H__
#define RBT_RED         0
#define RBT_BLACK       1

/* Red-Black tree node */
struct rbt_node {
        unsigned long  rbt_parent_color;
        struct rbt_node *rbt_left;
        struct rbt_node *rbt_right;
};

struct rbt_root {
        struct rbt_node *root;
};

#define rbt_parent(r)   ((struct rbt_node *)((r)->rbt_parent_color & (~3)))
#define rbt_color(r)   ((r)->rbt_parent_color & 1)
#define rbt_is_red(r)   (!rbt_color(r))
#define rbt_is_black(r) rbt_color(r)
#define rbt_set_red(r)  do { (r)->rbt_parent_color &= ~1; } while (0)
#define rbt_set_black(r)  do { (r)->rbt_parent_color |= 1; } while (0)

static inline void rbt_set_parent(struct rbt_node *rb, struct rbt_node *p)
{
        rb->rbt_parent_color = (rb->rbt_parent_color & 3) | (unsigned long)p;
}
static inline void rbt_set_color(struct rbt_node *rb, int color)
{
        rb->rbt_parent_color = (rb->rbt_parent_color & (~1)) | color;
}

#define RBT_ROOT        (struct rbt_root) { NULL, }
#define rbt_entry(ptr, type, member) container_of(ptr, type, member)

#define RBT_EMPTY_ROOT(root)    ((root)->rbt_node == NULL)
#define RBT_EMPTY_NODE(node)    (rbt_parent(node) == node)
#define RBT_CLEAR_NODE(node)    (rbt_set_parent(node, node))

void rbt_link_node(struct rbt_node * node, struct rbt_node * parent, struct rbt_node ** rbt_link);
void rbt_insert_color(struct rbt_node *node, struct rbt_root *root);
void rbt_erase(struct rbt_node *node, struct rbt_root *root);

/*
 * This function returns the first node (in sort order) of the tree.
 */
static inline struct rbt_node *rbt_first(const struct rbt_root *rbt)
{
        struct rbt_node *n;

        n = rbt->root;
        if (!n)
                return NULL;
        while (n->rbt_left)
                n = n->rbt_left;
        return n;
}

static inline struct rbt_node *rbt_next(const struct rbt_node *node)
{
        struct rbt_node *parent;

        if (rbt_parent(node) == node)
                return NULL;

        /* If we have a right-hand child, go down and then left as far
           as we can. */
        if (node->rbt_right) {
                node = node->rbt_right;
                while (node->rbt_left)
                        node=node->rbt_left;
                return (struct rbt_node *)node;
        }

        /* No right-hand children.  Everything down and left is
           smaller than us, so any 'next' node must be in the general
           direction of our parent. Go up the tree; any time the
           ancestor is a right-hand child of its parent, keep going
           up. First time it's a left-hand child of its parent, said
           parent is our 'next' node. */
        for (parent = rbt_parent(node); parent && node == parent->rbt_right; parent = rbt_parent(node))
                node = parent;

        return parent;
}

#endif /* !LIB_RBT_H__ */
