#
# Copyright 2016, NICTA
#
# This software may be distributed and modified according to the terms of
# the GNU General Public License version 2. Note that NO WARRANTY is provided.
# See "LICENSE_GPLv2.txt" for details.
#
# @TAG(NICTA_GPL)
#

MODULE=cgext2fs

ROOT_DIR=../../../

ifeq ($(KERNELRELEASE),)
# this include won't make sense inside the kernel tree
include $(ROOT_DIR)build-env.mk
endif

OUTPUT=generated
SRC=src/super.cogent
TYPES=data/types.txt
DEFNS=data/defns.txt
PROOF_ID=Ext2

# Standard Gum Directory
STDGUM=$(shell cogent --stdgum-dir)
# ADT headers required by Ext2fs
AHFILES=$(wildcard $(STDGUM)/gum/abstract/*.ah)
# ADT C files required by Ext2fs
LINUX_ACFILES=$(addprefix $(STDGUM)/gum/anti/, \
	common.ac \
	wordarray.ac \
	uarray.ac \
	array.ac \
	os.ac \
	ospage.ac \
	osbuffer.ac \
	iterator.ac \
	dls.ac) \
	plat/linux/wrapper.ac

# ADT C files required by verification
VERIF_ACFILES=plat/verification/wrapper.ac

ifndef KERNELDIR
KERNELDIR:= /lib/modules/$(shell uname -r)/build
endif

ifeq ($(KERNELRELEASE),)
PWD:= $(shell pwd)
endif

ifneq ($(DEBUG),)
EXTRA_CFLAGS+= -DEXT2FS_DEBUG
COGENT_FLAGS+= --debug
endif

# flags to ignores COGENT's compiler messy C code gen
COMMON_CFLAGS := -O2 -std=gnu99 -Wno-parentheses -Wno-declaration-after-statement -Wno-unused-variable -Wno-uninitialized
LINUX_EXTRA_CFLAGS := -I$(PWD)/plat/linux/ -I$(PWD) -I$(PWD)/src -I$(PWD)/lib -I$(PWD)/abstract $(COMMON_CFLAGS) -I$(STDGUM)
VERIF_EXTRA_CFLAGS := -I$(PWD)/plat/verification/ -I$(PWD) -I$(PWD)/src -I$(PWD)/lib -I$(PWD)/abstract -I$(STDGUM) $(COMMON_CFLAGS)

# COGENT flags
COGENT_FLAGS+= -Od --fno-static-inline --fno-fncall-as-macro --ffunc-purity-attr
# end of configuration

override COGENT_FLAGS+= -o$(OUTPUT) \
			--root-dir=$(ROOT_DIR) \
			--entry-funcs=$(DEFNS) \
			--ext-types=$(TYPES) \
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
# NOTE: A module.o is relevant only for the linux platform
OBJ?=plat/linux/module.o


###########################
# TARGET-SPECIFIC VARIABLES
###########################
# ACFILES
linux: ACFILES = $(LINUX_ACFILES)
.c-gen: ACFILES = $(LINUX_ACFILES)
verification: ACFILES = $(VERIF_ACFILES)
.verif-gen: ACFILES = $(VERIF_ACFILES)
# DISTDIR
linux: DIST_DIR = plat/linux
.c-gen: DIST_DIR = plat/linux
verification: DIST_DIR = plat/verification
.verif-gen: DIST_DIR = plat/verification
# EXTRA_CFLAGS
linux: EXTRA_CFLAGS = $(LINUX_EXTRA_CFLAGS)
.c-gen: EXTRA_CFLAGS = $(LINUX_EXTRA_CFLAGS)
verification: EXTRA_CFLAGS = $(VERIF_EXTRA_CFLAGS)
.verif-gen: EXTRA_CFLAGS = $(VERIF_EXTRA_CFLAGS)


# call from kernel build system
ifneq ($(KERNELRELEASE),)
	obj-m+= $(MODULE).o
	$(MODULE)-objs := $(OBJ)
else

PWD:= $(shell pwd)

.PHONY: default cogent clean .c-gen .verif-gen verification

default: linux

all: .c-gen $(OBJ)
	$(CC) -o $(NAME) $(OBJ)

%.c:
	$(CC) -c $@

# generate executable C code
.c-gen:
	cogent $(SRC) -g $(COGENT_FLAGS) \
		--cpp-args="\$$CPPIN -o \$$CPPOUT -E -P $(EXTRA_CFLAGS)" \
		--dist-dir=$(DIST_DIR) \
		--infer-c-funcs="$(ACFILES)"

.verif-gen:
	cogent $(SRC) -A $(COGENT_FLAGS) \
		--cpp-args="\$$CPPIN -o \$$CPPOUT -E -P $(EXTRA_CFLAGS)" \
		--dist-dir=$(DIST_DIR) \
		--infer-c-funcs="$(ACFILES)" \
		--proof-name=$(PROOF_ID) \
		--proof-input-c="wrapper_pp_inferred.c"

# compile Linux kernel module for file system
linux: .c-gen
	$(MAKE) OBJ="$(OBJ)" CFLAGS="$(CFLAGS)" EXTRA_CFLAGS="$(EXTRA_CFLAGS)" -C $(KERNELDIR) M=$(PWD) modules

# generate verification-clean C code and proof scripts
verification: .verif-gen
	mv $(DIST_DIR)/generated.table $(DIST_DIR)/wrapper_pp_inferred.table


clean:
	rm -f $(HOUTPUT)
	rm -f $(OBJ)
	rm -f $(RTMPC)
	rm -f $(RTMPPPC)
	rm -f $(MODULE).mod.[co] $(MODULE).o $(MODULE).ko Module.symvers modules.order
	rm -f abstract/*.h
	rm -rf *.thy ROOT generated.table BUILD_INFO
	find . -name *.thy -exec rm -f {} \;
	find . -name ROOT -exec rm -f {} \;
	find . -name BUILD_INFO -exec rm -f {} \;
	find . -name *_pp* -exec rm -f {} \;
	find . -name generated.* -exec rm -f {} \;

help:
	@echo "** Cogent ext2fs build help **"
	@echo "Run 'make' to build the Linux ext2fs kernel module."
	@echo ""
	@echo "Please run 'make <target>' where target is one of the following:"
	@echo "* linux"
	@echo "  Build the Linux kernel module(default)."
	@echo "  This will build against the kernel headers of the current running kernel."
	@echo "  Pass KERNELDIR=<path-to-kernel-headers> if you want to build against a different kernel version."
	@echo "  eg.:"
	@echo "     make linux"
	@echo "     make linux KERNELDIR=/usr/src/linux-headers-4.3.0-1-amd64/"
	@echo ""
	@echo "* debug"
	@echo "  Build the Linux kernel module with debugging enabled."
	@echo "  This is equivalent to running 'make linux DEBUG=1'"
	@echo ""
	@echo "* verification"
	@echo "  Generate verification table."
	@echo ""
	@echo "* clean"
	@echo "  Cleanup."
	@echo ""
	@echo "* help"
	@echo "  Print this help."

endif
