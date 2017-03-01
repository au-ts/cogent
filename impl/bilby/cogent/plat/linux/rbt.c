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

#include <lib/c/rbt.h>

void rbt_link_node(struct rbt_node * node, struct rbt_node * parent,
                  struct rbt_node ** rbt_link)
{
	node->rbt_parent_color = (unsigned long )parent;
	node->rbt_left = NULL;
	node->rbt_right = NULL;
	*rbt_link = node;
}

static void __rbt_rotate_left(struct rbt_node *node, struct rbt_root *rbt)
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
		rbt->root = right;
	rbt_set_parent(node, right);
}

static void __rbt_rotate_right(struct rbt_node *node, struct rbt_root *rbt)
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
		rbt->root = left;
	rbt_set_parent(node, left);
}

void rbt_insert_color(struct rbt_node *node, struct rbt_root *rbt)
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
				__rbt_rotate_left(parent, rbt);
				tmp = parent;
				parent = node;
				node = tmp;
			}

			rbt_set_black(parent);
			rbt_set_red(gparent);
			__rbt_rotate_right(gparent, rbt);
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
				__rbt_rotate_right(parent, rbt);
				tmp = parent;
				parent = node;
				node = tmp;
			}

			rbt_set_black(parent);
			rbt_set_red(gparent);
			__rbt_rotate_left(gparent, rbt);
		}
	}

	rbt_set_black(rbt->root);
}

static void __rbt_erase_color(struct rbt_node *node, struct rbt_node *parent,
			     struct rbt_root *rbt)
{
	struct rbt_node *other;

	while ((!node || rbt_is_black(node)) && node != rbt->root)
	{
		if (parent->rbt_left == node)
		{
			other = parent->rbt_right;
			if (rbt_is_red(other))
			{
				rbt_set_black(other);
				rbt_set_red(parent);
				__rbt_rotate_left(parent, rbt);
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
					__rbt_rotate_right(other, rbt);
					other = parent->rbt_right;
				}
				rbt_set_color(other, rbt_color(parent));
				rbt_set_black(parent);
				rbt_set_black(other->rbt_right);
				__rbt_rotate_left(parent, rbt);
				node = rbt->root;
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
				__rbt_rotate_right(parent, rbt);
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
					__rbt_rotate_left(other, rbt);
					other = parent->rbt_left;
				}
				rbt_set_color(other, rbt_color(parent));
				rbt_set_black(parent);
				rbt_set_black(other->rbt_left);
				__rbt_rotate_right(parent, rbt);
				node = rbt->root;
				break;
			}
		}
	}
	if (node)
		rbt_set_black(node);
}

void rbt_erase(struct rbt_node *node, struct rbt_root *rbt)
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
			rbt->root = node;

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
                        __rbt_erase_color(child, parent, rbt);
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
		rbt->root = child;

	if (color == RBT_BLACK)
		__rbt_erase_color(child, parent, rbt);
}
