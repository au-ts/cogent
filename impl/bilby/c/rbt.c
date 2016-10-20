/*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 */

/*
  Red Black Trees
  (C) 1999  Andrea Arcangeli <andrea@suse.de>
  (C) 2002  David Woodhouse <dwmw2@infradead.org>

  This program is free software; you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation; either version 2 of the License, or
  (at your option) any later version.

  This program is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with this program; if not, write to the Free Software
  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA

*/

#include <bilbyfs.h>

static inline void rbt_init_node(struct rbt_node *rb)
{
	rb->rbt_parent_color = 0;
	rb->rbt_right = NULL;
	rb->rbt_left = NULL;
	RBT_CLEAR_NODE(rb);
}

void rbt_link_node(struct rbt_node * node, struct rbt_node * parent,
                  struct rbt_node ** rbt_link)
{
	node->rbt_parent_color = (unsigned long )parent;
	node->rbt_left = NULL;
	node->rbt_right = NULL;
	*rbt_link = node;
}

static void __rbt_rotate_left(struct rbt_node *node, struct rbt_root *root)
{
	struct rbt_node *right = node->rbt_right;
	struct rbt_node *parent = rbt_parent(node);

        node->rbt_right = right->rbt_left;
	if (node->rbt_right)
		rbt_set_parent(right->rbt_left, node);
	right->rbt_left = node;

	rbt_set_parent(right, parent);

	if (parent)
	{
		if (node == parent->rbt_left)
			parent->rbt_left = right;
		else
			parent->rbt_right = right;
	}
	else
		root->rbt_node = right;
	rbt_set_parent(node, right);
}

static void __rbt_rotate_right(struct rbt_node *node, struct rbt_root *root)
{
	struct rbt_node *left = node->rbt_left;
	struct rbt_node *parent = rbt_parent(node);

        node->rbt_left = left->rbt_right;
	if (node->rbt_left)
		rbt_set_parent(left->rbt_right, node);
	left->rbt_right = node;

	rbt_set_parent(left, parent);

	if (parent)
	{
		if (node == parent->rbt_right)
			parent->rbt_right = left;
		else
			parent->rbt_left = left;
	}
	else
		root->rbt_node = left;
	rbt_set_parent(node, left);
}

void rbt_insert_color(struct rbt_node *node, struct rbt_root *root)
{
	struct rbt_node *parent, *gparent;

	for (parent = rbt_parent(node); parent && rbt_is_red(parent); parent = rbt_parent(node))
	{
		gparent = rbt_parent(parent);

		if (parent == gparent->rbt_left)
		{
			{
				register struct rbt_node *uncle = gparent->rbt_right;
				if (uncle && rbt_is_red(uncle))
				{
					rbt_set_black(uncle);
					rbt_set_black(parent);
					rbt_set_red(gparent);
					node = gparent;
					continue;
				}
			}

			if (parent->rbt_right == node)
			{
				register struct rbt_node *tmp;
				__rbt_rotate_left(parent, root);
				tmp = parent;
				parent = node;
				node = tmp;
			}

			rbt_set_black(parent);
			rbt_set_red(gparent);
			__rbt_rotate_right(gparent, root);
		} else {
			{
				register struct rbt_node *uncle = gparent->rbt_left;
				if (uncle && rbt_is_red(uncle))
				{
					rbt_set_black(uncle);
					rbt_set_black(parent);
					rbt_set_red(gparent);
					node = gparent;
					continue;
				}
			}

			if (parent->rbt_left == node)
			{
				register struct rbt_node *tmp;
				__rbt_rotate_right(parent, root);
				tmp = parent;
				parent = node;
				node = tmp;
			}

			rbt_set_black(parent);
			rbt_set_red(gparent);
			__rbt_rotate_left(gparent, root);
		}
	}

	rbt_set_black(root->rbt_node);
}

static void __rbt_erase_color(struct rbt_node *node, struct rbt_node *parent,
			     struct rbt_root *root)
{
	struct rbt_node *other;

	while ((!node || rbt_is_black(node)) && node != root->rbt_node)
	{
		if (parent->rbt_left == node)
		{
			other = parent->rbt_right;
			if (rbt_is_red(other))
			{
				rbt_set_black(other);
				rbt_set_red(parent);
				__rbt_rotate_left(parent, root);
				other = parent->rbt_right;
			}
			if ((!other->rbt_left || rbt_is_black(other->rbt_left)) &&
			    (!other->rbt_right || rbt_is_black(other->rbt_right)))
			{
				rbt_set_red(other);
				node = parent;
				parent = rbt_parent(node);
			}
			else
			{
				if (!other->rbt_right || rbt_is_black(other->rbt_right))
				{
					rbt_set_black(other->rbt_left);
					rbt_set_red(other);
					__rbt_rotate_right(other, root);
					other = parent->rbt_right;
				}
				rbt_set_color(other, rbt_color(parent));
				rbt_set_black(parent);
				rbt_set_black(other->rbt_right);
				__rbt_rotate_left(parent, root);
				node = root->rbt_node;
				break;
			}
		}
		else
		{
			other = parent->rbt_left;
			if (rbt_is_red(other))
			{
				rbt_set_black(other);
				rbt_set_red(parent);
				__rbt_rotate_right(parent, root);
				other = parent->rbt_left;
			}
			if ((!other->rbt_left || rbt_is_black(other->rbt_left)) &&
			    (!other->rbt_right || rbt_is_black(other->rbt_right)))
			{
				rbt_set_red(other);
				node = parent;
				parent = rbt_parent(node);
			}
			else
			{
				if (!other->rbt_left || rbt_is_black(other->rbt_left))
				{
					rbt_set_black(other->rbt_right);
					rbt_set_red(other);
					__rbt_rotate_left(other, root);
					other = parent->rbt_left;
				}
				rbt_set_color(other, rbt_color(parent));
				rbt_set_black(parent);
				rbt_set_black(other->rbt_left);
				__rbt_rotate_right(parent, root);
				node = root->rbt_node;
				break;
			}
		}
	}
	if (node)
		rbt_set_black(node);
}

void rbt_erase(struct rbt_node *node, struct rbt_root *root)
{
	struct rbt_node *child, *parent;
	int color;

	if (!node->rbt_left)
		child = node->rbt_right;
	else if (!node->rbt_right)
		child = node->rbt_left;
	else
	{
		struct rbt_node *old = node, *left;

		node = node->rbt_right;
		for (left = node->rbt_left; left != NULL; left = node->rbt_left)
			node = left;

		if (rbt_parent(old)) {
			if (rbt_parent(old)->rbt_left == old)
				rbt_parent(old)->rbt_left = node;
			else
				rbt_parent(old)->rbt_right = node;
		} else
			root->rbt_node = node;

		child = node->rbt_right;
		parent = rbt_parent(node);
		color = rbt_color(node);

		if (parent == old) {
			parent = node;
		} else {
			if (child)
				rbt_set_parent(child, parent);
			parent->rbt_left = child;

			node->rbt_right = old->rbt_right;
			rbt_set_parent(old->rbt_right, node);
		}

		node->rbt_parent_color = old->rbt_parent_color;
		node->rbt_left = old->rbt_left;
		rbt_set_parent(old->rbt_left, node);

                if (color == RBT_BLACK)
                        __rbt_erase_color(child, parent, root);
                return;
	}

	parent = rbt_parent(node);
	color = rbt_color(node);

	if (child)
		rbt_set_parent(child, parent);
	if (parent)
	{
		if (parent->rbt_left == node)
			parent->rbt_left = child;
		else
			parent->rbt_right = child;
	}
	else
		root->rbt_node = child;

	if (color == RBT_BLACK)
		__rbt_erase_color(child, parent, root);
}

/*
 * This function returns the first node (in sort order) of the tree.
 */
struct rbt_node *rbt_first(const struct rbt_root *root)
{
	struct rbt_node	*n;

	n = root->rbt_node;
	if (!n)
		return NULL;
	while (n->rbt_left)
		n = n->rbt_left;
	return n;
}

struct rbt_node *rbt_last(const struct rbt_root *root)
{
	struct rbt_node	*n;

	n = root->rbt_node;
	if (!n)
		return NULL;
	while (n->rbt_right)
		n = n->rbt_right;
	return n;
}

struct rbt_node *rbt_next(const struct rbt_node *node)
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

struct rbt_node *rbt_prev(const struct rbt_node *node)
{
	struct rbt_node *parent;

	if (rbt_parent(node) == node)
		return NULL;

	/* If we have a left-hand child, go down and then right as far
	   as we can. */
	if (node->rbt_left) {
		node = node->rbt_left;
		while (node->rbt_right)
			node=node->rbt_right;
		return (struct rbt_node *)node;
	}

	/* No left-hand children. Go up till we find an ancestor which
	   is a right-hand child of its parent */
	for (parent = rbt_parent(node);  parent && node == parent->rbt_left; parent = rbt_parent(node))
		node = parent;

	return parent;
}

void rbt_replace_node(struct rbt_node *victim, struct rbt_node *new,
		     struct rbt_root *root)
{
	struct rbt_node *parent = rbt_parent(victim);

	/* Set the surrounding nodes to point to the replacement */
	if (parent) {
		if (victim == parent->rbt_left)
			parent->rbt_left = new;
		else
			parent->rbt_right = new;
	} else {
		root->rbt_node = new;
	}
	if (victim->rbt_left)
		rbt_set_parent(victim->rbt_left, new);
	if (victim->rbt_right)
		rbt_set_parent(victim->rbt_right, new);

	/* Copy the pointers/colour from the victim to the replacement */
	*new = *victim;
}
