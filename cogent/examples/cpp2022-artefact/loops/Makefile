NAME=test

SRC=test.cogent
OUTPUT=test
COUTPUT=$(addsuffix .c, $(OUTPUT))
HOUTPUT=$(addsuffix .h, $(OUTPUT))

AHFILES=WordArray.ah

ACFILES=main.ac

LIBGUM=$(shell cogent --libgum-dir)

PP=$(ACFILES:.ac=_pp.ac)
PPINFER=$(ACFILES:.ac=_pp_inferred.c)

OBJ=$(PPINFER:.c=.o)

CFLAGS+=-I. -I$(LIBGUM) -I$(BUILDDIR) -std=gnu99

BUILDDIR=build
ABSDIR=abstract

.PHONY: default cogent clean gen-anti test
.SECONDARY:

default: all

all:
	mkdir -p $(BUILDDIR)
	mkdir -p "$(BUILDDIR)/$(ABSDIR)"
	cogent -A -g -Od -ogenerated \
		--infer-c-types="$(AHFILES)" \
		--abs-type-dir="$(BUILDDIR)" \
		--Wno-warn --infer-c-funcs="$(ACFILES)" \
		--cpp="$(CPP)" \
		--cpp-args="-x c \$$CPPIN -o \$$CPPOUT -E -P $(CFLAGS)" \
		--proof-input-c=$(PPINFER) \
	    --dist-dir=$(BUILDDIR) \
		--entry-funcs=entrypoints.cfg $(SRC) 
	cp build/generated.table build/main_pp_inferred.table
	sed -i "s/^typedecl 'a WordArray.*/datatype 'a WordArray = SWA \"'a list \"/" "$(BUILDDIR)/Generated_ShallowShared.thy"
	sed -i "/^(\* Put manual type and value relations below.*/a instantiation WordArray_u32_C :: cogent_C_val\nbegin\ndefinition type_rel_WordArray_u32_C_def:\n  \"type_rel typ (_ :: WordArray_u32_C itself) \\\<equiv> typ = RCon ''WordArray'' \[RPrim (Num U32)\]\"\ndefinition val_rel_WordArray_u32_C_def:\n  \"val_rel uv (x :: WordArray_u32_C) \\\<equiv> (\\\<exists>len arr. uv = UAbstract (UWA (TPrim (Num U32)) len arr) \\\<and> len = (SCAST(32 signed \\\<rightarrow> 32)(len_C x)) \\\<and> arr = ptr_val (values_C x))\"\ninstance ..\nend" "$(BUILDDIR)/Generated_CorresSetup.thy"
	sed -i "s/^local_setup \\\<open> local_setup_val_rel_type_rel_put_them_in_buckets \"main_pp_inferred\.c\" \[\] \\\<close>.*/local_setup \\\<open> local_setup_val_rel_type_rel_put_them_in_buckets \"main_pp_inferred.c\" \[UAbstract \"WordArray_u32\"\] \\\<close>/" "$(BUILDDIR)/Generated_CorresSetup.thy"
	sed -i "s/^local_setup \\\<open> local_setup_heap_rel \"main_pp_inferred\.c\" \[\] \[\] \\\<close>.*/local_setup \\\<open> local_setup_heap_rel \"main_pp_inferred.c\" \[\"WordArray_u32_C\"\] \[(\"32 word\", \"w32\")\] \\\<close>/" "$(BUILDDIR)/Generated_CorresSetup.thy"
	sed -i "/^(\* Put manual value relation definitions below.*/a \ \ val_rel_WordArray_u32_C_def" "$(BUILDDIR)/Generated_CorresSetup.thy"
	sed -i "/^(\* Put manual type relation definitions below.*/a \ \ type_rel_WordArray_u32_C_def" "$(BUILDDIR)/Generated_CorresSetup.thy"

clean:
	rm -r $(BUILDDIR)
