#
# Copyright 2016, NICTA
#
# This software may be distributed and modified according to the terms of
# the GNU General Public License version 2. Note that NO WARRANTY is provided.
# See "LICENSE_GPLv2.txt" for details.
#
# @TAG(NICTA_GPL)
#

MODULE=cgbilbyfs

ROOT_DIR=../../../../../

ifeq ($(KERNELRELEASE),)
# this include won't make sense inside the kernel tree
include $(ROOT_DIR)build-env.mk
endif

OUTPUT=generated
SRC=fsm.cogent
DEFNS=defns.txt

# Standard Gum Directory
STDGUM=$(COGENT_STD_GUM_DIR)
# ADT headers required by BilbyFs
AHFILES=$(wildcard $(STDGUM)/gum/anti/abstract/*.ah)
# ADT C files required by BilbyFs
LINUX_ACFILES=$(addprefix $(STDGUM)/gum/anti/, \
		common.ac \
		wordarray.ac \
		array.ac \
		rbt.ac ) \
		fsm_wrapper.ac
# ADT C files required by verification
LINUX_TYPES=types.txt

ifeq ($(KERNELRELEASE),)
PWD:= $(shell pwd)
endif
ifneq ($(DEBUG),)
EXTRA_CFLAGS+= -DBILBYFS_DEBUG
COGENT_FLAGS+= --debug
endif

# flags to ignores COGENT's compiler messy C code gen
COMMON_CFLAGS := -O2 -Wno-parentheses -Wno-declaration-after-statement -Wno-unused-variable -Wno-uninitialized
LINUX_EXTRA_CFLAGS := -I$(PWD) -I$(PWD)/build -I$(PWD)/abstract $(COMMON_CFLAGS) -I$(STDGUM)

# COGENT flags
COGENT_FLAGS+= -Od --fno-static-inline --fno-fncall-as-macro --fnormalisation=knf --ffunc-purity-attr
# end of configuration

override COGENT_FLAGS+= -o$(OUTPUT) \
			--root-dir=$(ROOT_DIR) \
			--entry-funcs=$(DEFNS) \
			--infer-c-types="$(AHFILES)" \
			--abs-type-dir=$(PWD)

COUTPUT=$(addsuffix .c, $(OUTPUT))
HOUTPUT=$(addsuffix .h, $(OUTPUT))
NAME=$(MODULE)
RTMPC=$(ACFILES:.ac=_pp_inferred.c)
RTMPPPC=$(COUTPUT) $(ACFILES:.ac=_pp.ac)

BUILDSRC=$(wildcard build/*.c)
# Add C files with no antiquotation to OBJ.
# Writing these functions in a .ac file would lead defining multiple
# times the same symbol when parametric polymorphism gets expanded.


# ACFILES
ACFILES = $(LINUX_ACFILES)
# DISTDIR
DIST_DIR = build
# EXTRA_CFLAGS
EXTRA_CFLAGS = $(LINUX_EXTRA_CFLAGS)

# call from kernel build system
ifneq ($(KERNELRELEASE),)
  obj-m	+= $(MODULE).o
  $(MODULE)-objs := $(OBJ)
else

PWD:= $(shell pwd)

.PHONY: default all clean c-gen o-gen hs-gen


default: c-gen o-gen hs-gen
all: c-gen o-gen hs-gen

# generate executable C code
# NOTE: We run cpp with in c99 mode, as the default mode that cpp runs in is gnu99,
#       which has an issue when parsing. It replaces anything 'linux' with a '1'.
#       More details here: http://stackoverflow.com/questions/19210935/why-does-the-c-preprocessor-interpret-the-word-linux-as-the-constant-1
#       So we use c99 mode here and when building the generated C code(make modules), we
#       use `gnu99` mode.
c-gen:
	$(Q)cogent $(SRC) -g $(COGENT_FLAGS) \
				--cpp-args="-std=c99 \$$CPPIN -o \$$CPPOUT -E -P $(EXTRA_CFLAGS)" \
				--dist-dir=$(DIST_DIR) \
				--infer-c-funcs="$(ACFILES)" \
				--ext-types="$(LINUX_TYPES)"

o-gen:
	$(Q)$(CC) -c $(DIST_DIR)/fsm_wrapper_pp_inferred.c -o $(DIST_DIR)/fsm.o -I$(DIST_DIR) -I$(PWD) -fPIC

hs-gen:
	$(Q)cogent $(SRC) --hs-shallow-desugar $(COGENT_FLAGS) \
				--dist-dir=$(DIST_DIR)

clean:
	$(E) "Cleaning up.."
	$(Q)rm -f abstract/*.h
	$(Q)rm -rf $(DIST_DIR)

endif
