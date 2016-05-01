/*
 * @TAG(OTHER_GPL)
 */

/* 
  Modified file of:
-------------------------------------------------
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

#ifndef _RBT_H_
#define _RBT_H_

/* Red-Black tree node */
struct rbt_node {
        unsigned long  rbt_parent_color;
#define RBT_RED         0
#define RBT_BLACK       1
        struct rbt_node *rbt_left;
        struct rbt_node *rbt_right;
};

#endif
