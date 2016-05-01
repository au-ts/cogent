#
# Copyright 2016, NICTA
#
# This software may be distributed and modified according to the terms of
# the GNU General Public License version 2. Note that NO WARRANTY is provided.
# See "LICENSE_GPLv2.txt" for details.
#
# @TAG(NICTA_GPL)
#

ifeq ($(KERNELRELEASE),)
# this include won't make sense inside the kernel tree
include ../../../build-env.mk
endif

MODULE=cgbilbyfs
SHELL=bash

ROOT_DIR=../../../
OUTPUT=generated
DIST_DIR=.
SRC=fs/fsop.cogent
OS=linux
TYPES=types.txt
DEFNS=defns.txt
PROOF_ID=BilbyFS

# ADT headers required by BilbyFs
AHFILES=$(wildcard abstract/*.ah)
# ADT C files required by BilbyFs
ACFILES=$(addprefix libgum/anti/, common.ac wordarray.ac array.ac rbt.ac os.ac list.ac crc32.ac)
# WARNING: do not modify ACFILES; to include a .ac file, add a #include in wrapper.ac
ACFILES=os/linux/wrapper.ac
#DEBUG=1 # Run make DEBUG=1 or uncomment this line to enable debugging

ifeq ($(KERNELRELEASE),)
PWD:= $(shell pwd)
endif
ifneq ($(DEBUG),)
EXTRA_CFLAGS+= -DBILBYFS_DEBUG
COGENT_FLAGS+= --debug
endif

# include dirs
EXTRA_CFLAGS+= -I$(PWD)/os/$(OS)/ -I$(PWD) -I$(PWD)/fs -I$(PWD)/lib -I$(PWD)/abstract

# flags to ignores COGENT's compiler messy C code gen
EXTRA_CFLAGS+= -O2 -std=gnu99 -Wno-parentheses -Wno-declaration-after-statement -Wno-unused-variable -Wno-uninitialized

# COGENT flags
COGENT_FLAGS+= -Od --fno-static-inline --fno-fncall-as-macro --fnormalisation=knf --ffunc-purity-attr
# end of configuration

override COGENT_FLAGS+= -o$(OUTPUT) --root-dir=$(ROOT_DIR) --dist-dir=$(DIST_DIR) --entry-funcs=$(DEFNS) --ext-types=$(TYPES) --infer-c-types="$(AHFILES)" --cpp-args="\$$CPPIN -o \$$CPPOUT -E -P $(EXTRA_CFLAGS)"

COUTPUT=$(addsuffix .c, $(OUTPUT))
HOUTPUT=$(addsuffix .h, $(OUTPUT))
NAME=$(MODULE)
RTMPC=$(ACFILES:.ac=_pp_inferred.c)
RTMPPPC=$(COUTPUT) $(ACFILES:.ac=_pp.ac)

BUILDSRC=$(wildcard build/*.c)
# Add C files with no antiquotation to OBJ.
# Writing these functions in a .ac file would lead defining multiple
# times the same symbol when parametric polymorphism gets expanded.
OBJ?=os/$(OS)/module.o os/$(OS)/rbt.o

# call from kernel build system
ifneq ($(KERNELRELEASE),)
  obj-m	+= $(MODULE).o
  $(MODULE)-objs := $(OBJ)
else

KERNELDIR ?= /lib/modules/$(shell uname -r)/build
PWD:= $(shell pwd)

.PHONY: default cogent clean gen verification

default: gen linux

all: gen $(OBJ)
	$(CC) -o $(NAME) $(OBJ)

# generate executable C code
gen:
	cogent $(SRC) -g $(COGENT_FLAGS) --infer-c-funcs="$(ACFILES)"

# generate verification-clean C code and proof scripts
verification:
	cogent $(SRC) -A $(COGENT_FLAGS) \
		--infer-c-funcs="wrapper-verif.ac" \
		--proof-name=$(PROOF_ID) \
		--proof-input-c="wrapper-verif_pp_inferred.c"
	cp generated.table wrapper-verif_pp_inferred.table

%.c:
	$(CC) -c $@

# compile Linux kernel module for file system
linux:
	$(MAKE) OBJ="$(OBJ)" CFLAGS="$(CFLAGS) $(EXTRA_CFLAGS)" -C $(KERNELDIR) M=$(PWD) modules

clean:
	rm -f $(HOUTPUT)
	rm -f $(OBJ)
	rm -f $(RTMPC)
	rm -f $(RTMPPPC)
	rm -f $(MODULE).mod.[co] $(MODULE).o
	rm -f abstract/*.h
endif
