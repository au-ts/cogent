#
# Copyright 2017, NICTA
#
# This software may be distributed and modified according to the terms of
# the GNU General Public License version 2. Note that NO WARRANTY is provided.
# See "LICENSE_GPLv2.txt" for details.
#
# @TAG(NICTA_GPL)
#

NAME=weird_inc

SRC=weird_inc.cogent
OUTPUT=weird_inc  # $(SRC:.cogent=-gen)
COUTPUT=$(addsuffix .c, $(OUTPUT))
HOUTPUT=$(addsuffix .h, $(OUTPUT))
TABLE=$(addsuffix .table, $(OUTPUT))
NEWTABLE=$(addsuffix .table.new, $(OUTPUT))

CFLAGS=-I.  -std=gnu99  # -I../plat/console -I$(LIBGUM)/gum/anti

.PHONY: default cogent clean
.SECONDARY:

default: gen-c-proof

gen-c-proof:
	cogent $(SRC) --all -g --type-proof --c-refinement --root-dir=../../.. --fake-header-dir=../../lib

clean:
	rm -f $(COUTPUT) $(HOUTPUT) $(TABLE) $(NEWTABLE) 
	@# rm -f *-gen.*
	rm -f $(NAME)
	rm -f Weird_inc*thy
	rm -f ROOT
	rm -f BUILD_INFO
	rm -f umm_types.txt
