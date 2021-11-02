#
# Copyright 2017, NICTA
#
# This software may be distributed and modified according to the terms of
# the GNU General Public License version 2. Note that NO WARRANTY is provided.
# See "LICENSE_GPLv2.txt" for details.
#
# @TAG(NICTA_GPL)
#

NAME=wordarray

SRC=Sum.cogent
OUTPUT=Sum # $(SRC:.cogent=-gen)
COUTPUT=$(addsuffix .c, $(OUTPUT))
HOUTPUT=$(addsuffix .h, $(OUTPUT))

STDGUM=$(shell cogent --libgum-dir)

AHFILES=WordArray.ah
ACFILES=main.ac

PP=$(ACFILES:.ac=_pp.ac)
PPINFER=$(ACFILES:.ac=_pp_inferred.c)

ABSDIR=./abstract

OBJ=$(PPINFER:.c=.o)

CFLAGS+=-I. -I$(STDGUM) -I$(STDGUM)/gum/anti -std=gnu99

.PHONY: default cogent clean gen-anti test
.SECONDARY:

default: all

all:
	mkdir -p $(ABSDIR)
	cogent -A -g -Od -ogenerated \
		--infer-c-types="$(AHFILES)" \
		--Wno-warn --infer-c-funcs="$(ACFILES)" \
		--cpp-args="\$$CPPIN -o \$$CPPOUT -E -P $(CFLAGS)" \
		--proof-input-c=$(PPINFER) \
		--entry-funcs=entrypoints.cfg $(SRC)
	cp generated.table main_pp_inferred.table
	sed -i "s/^typedecl 'a WordArray.*/type_synonym 'a WordArray = \"'a list \"/" "Generated_ShallowShared.thy"
	sed -i "/^(\* Put manual type and value relations below.*/a instantiation WordArray_u32_C :: cogent_C_val\nbegin\ndefinition type_rel_WordArray_u32_C_def:\n  \"type_rel typ (_ :: WordArray_u32_C itself) \\\<equiv> typ = RCon ''WordArray'' \[RPrim (Num U32)\]\"\ndefinition val_rel_WordArray_u32_C_def:\n  \"val_rel uv (x :: WordArray_u32_C) \\\<equiv> (\\\<exists>len arr. uv = UAbstract (UWA (TPrim (Num U32)) len arr) \\\<and> len = (SCAST(32 signed \\\<rightarrow> 32)(len_C x)) \\\<and> arr = ptr_val (values_C x))\"\ninstance ..\nend" "Generated_CorresSetup.thy"
	sed -i "s/^local_setup \\\<open> local_setup_val_rel_type_rel_put_them_in_buckets \"main_pp_inferred\.c\" \[\] \\\<close>.*/local_setup \\\<open> local_setup_val_rel_type_rel_put_them_in_buckets \"main_pp_inferred.c\" \[UAbstract \"WordArray_u32\"\] \\\<close>/" "Generated_CorresSetup.thy"
	sed -i "s/^local_setup \\\<open> local_setup_heap_rel \"main_pp_inferred\.c\" \[\] \[\] \\\<close>.*/local_setup \\\<open> local_setup_heap_rel \"main_pp_inferred.c\" \[\"WordArray_u32_C\"\] \[(\"32 word\", \"w32\")\] \\\<close>/" "Generated_CorresSetup.thy"
	sed -i "/^(\* Put manual value relation definitions below.*/a \ \ val_rel_WordArray_u32_C_def" "Generated_CorresSetup.thy"
	sed -i "/^(\* Put manual type relation definitions below.*/a \ \ type_rel_WordArray_u32_C_def" "Generated_CorresSetup.thy"

clean:
	rm -r $(ABSDIR) ROOT generated* BUILD_INFO main_pp* Generated*
