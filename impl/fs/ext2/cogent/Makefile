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

ROOT_DIR=../../../../

ifeq ($(KERNELRELEASE),)
# this include won't make sense inside the kernel tree
include $(ROOT_DIR)build-env.mk
endif

OUTPUT=ext2
SRC=src/super.cogent
TYPES=data/types.txt
DEFNS=data/defns.txt
PROOF_ID=Ext2

# GCC version
GCCVER:=$(shell gcc -dumpversion)
# Standard Gum Directory
LIBGUM:=$(COGENT_LIBGUM_DIR)
ifeq ($(LIBGUM),)
LIBGUM:=$(shell cogent --libgum-dir)
endif

COGENT_SOURCES := $(addprefix src/,\
		 balloc.cogent bchain.cogent \
		 dcommon.cogent debug.cogent \
		 dread.cogent dwrite.cogent \
		 ext2.cogent groupdesc.cogent \
		 ialloc.cogent indirect.cogent \
		 iread.cogent iwrite.cogent \
		 path.cogent super.cogent \
		 test.cogent util.cogent)
C_SOURCES := $(addprefix plat/linux/, \
		adt.h \
		alloc.ac \
		inode.ac \
		module.c \
		vfs.ac \
		wrapper.h)

# ADT headers required by Ext2fs
AHFILES=$(wildcard $(LIBGUM)/gum/anti/abstract/*.ah)
# ADT C files required by Ext2fs
LINUX_ACFILES=$(addprefix $(LIBGUM)/gum/anti/, \
	common.ac \
	wordarray.ac \
	uarray.ac \
	array.ac \
	os.ac \
	ospage.ac \
	osbuffer.ac \
	iterator.ac \
	log.ac \
	dls.ac) \
	plat/linux/wrapper.ac

COGENT_GUM := $(wildcard $(LIBGUM)/gum/*/*.cogent $(LIBGUM)/gum/kernel/linux/*.cogent)

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
# COGENT_FLAGS+= --debug
endif

# flags to ignores COGENT's compiler messy C code gen
EXTRA_CFLAGS	+= -O2 -Wno-parentheses -Wno-declaration-after-statement -Wno-unused-variable -Wno-uninitialized

CPPFLAGS.common	:= -I$(PWD) -I$(PWD)/src -I$(PWD)/lib -I$(PWD)/abstract -I$(LIBGUM)
CPPFLAGS.linux	:= -I$(PWD)/plat/linux/
CPPFLAGS.verif	:= -I$(PWD)/plat/verification/ -DVERIFICATION

# COGENT flags
COGENT_FLAGS+= -Od --fno-static-inline --fno-fncall-as-macro \
		--ffunc-purity-attr --fno-pretty-errmsgs
# end of configuration

override COGENT_FLAGS+= -o$(OUTPUT) \
			--root-dir=$(ROOT_DIR) \
			--entry-funcs=$(DEFNS) \
			--ext-types=$(TYPES) \
			--infer-c-types="$(AHFILES)" \
			--abs-type-dir=$(PWD) \
			--cpp-args="-std=c99 \$$CPPIN -o \$$CPPOUT -E -P ${CFLAGS} ${EXTRA_CFLAGS} ${CPPFLAGS}" \
			--cogent-pp-args="${CPPFLAGS}"

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
# CPPFLAGS
linux        .c-gen:     CPPFLAGS = ${CPPFLAGS.common} ${CPPFLAGS.linux}
verification .verif-gen: CPPFLAGS = ${CPPFLAGS.common} ${CPPFLAGS.verif}


# call from kernel build system
ifneq ($(KERNELRELEASE),)
	ccflags-y+=-I/usr/lib/gcc/x86_64-pc-linux-gnu/$(GCCVER)/include
	obj-m+= $(MODULE).o
	$(MODULE)-objs := $(OBJ)
else

PWD:= $(shell pwd)

.PHONY: default cogent clean .c-gen .verif-gen verification

default: linux

all: .c-gen $(OBJ)
	$(Q)$(CC) -o $(NAME) $(OBJ)

%.c:
	$(Q)$(CC) -c $@

# generate executable C code
# NOTE: We run cpp with in c99 mode, as the default mode that cpp runs in is gnu99,
#       which has an issue when parsing. It replaces anything 'linux' with a '1'.
#       More details here: http://stackoverflow.com/questions/19210935/why-does-the-c-preprocessor-interpret-the-word-linux-as-the-constant-1
#       So we use c99 mode here and when building the generated C code(make modules), we
#       use `gnu99` mode.
.c-gen: ${COGENT_SOURCES} ${C_SOURCES} ${LINUX_ACFILES} ${COGENT_GUM}
	$(Q)cogent $(SRC) -g $(COGENT_FLAGS) \
		--dist-dir=$(DIST_DIR) \
		--infer-c-funcs="$(ACFILES)"
	$(Q)touch $@

.verif-gen: ${COGENT_SOURCES} ${C_SOURCES} ${LINUX_ACFILES} ${COGENT_GUM}
	$(Q)cogent $(SRC) -A $(COGENT_FLAGS) \
		--dist-dir=$(DIST_DIR) \
		--infer-c-funcs="$(ACFILES)" \
		--proof-name=$(PROOF_ID) \
		--proof-input-c="wrapper_pp_inferred.c" \
		--fno-simplify-shallow-tuples
	$(Q)touch $@

# compile Linux kernel module for file system
linux: .c-gen
	$(Q)$(MAKE) OBJ="$(OBJ)" CFLAGS="${CFLAGS}" EXTRA_CFLAGS="-std=gnu99 ${EXTRA_CFLAGS} ${CPPFLAGS}" -C $(KERNELDIR) M=$(PWD) modules

# generate verification-clean C code and proof scripts
verification: .verif-gen
	$(Q)mv $(DIST_DIR)/$(OUTPUT).table $(DIST_DIR)/wrapper_pp_inferred.table


clean:
	$(E) "Cleaning up.."
	$(Q)rm -f $(HOUTPUT)
	$(Q)rm -f $(OBJ)
	$(Q)rm -f $(RTMPC)
	$(Q)rm -f $(RTMPPPC)
	$(Q)rm -f $(MODULE).mod.[co] $(MODULE).o $(MODULE).ko Module.symvers modules.order
	$(Q)rm -f abstract/*.h
	$(Q)rm -rf *.thy ROOT $(OUTPUT).table BUILD_INFO
	$(Q)find . -name *.thy -exec rm -f {} \;
	$(Q)find . -name ROOT -exec rm -f {} \;
	$(Q)find . -name BUILD_INFO -exec rm -f {} \;
	$(Q)find . -name *_pp* -exec rm -f {} \;
	$(Q)find . -name $(OUTPUT).[ch] -exec rm -f {} \;
	$(Q)find . -name *.cmd -exec rm -f {} \;

TAGS: $(COGENT_SOURCES) $(C_SOURCES) $(LINUX_ACFILES) $(COGENT_GUM) Makefile
	etags --regex='/^type *\([a^[b-zA-Z_][a-zA-Z0-9_]*\) .*= .*$$\|^\([a-zA-Z][a-zA-Z0-9_]*\) .*=.*$$/\1\2/' $(COGENT_SOURCES) $(COGENT_GUM)
	etags --append $(filter %.c,$(C_SOURCES) $(LINUX_ACFILES))
	etags --append -l c --regex='/^\(\$$ty:(.*) *\)?\(\$$id:\)?\([A-Za-z_][A-Za-z0-9_]*\) *(.*$$/\3/' $(filter %.ac,$(C_SOURCES) $(LINUX_ACFILES))

help:
	$(E) "** Cogent ext2fs build help **"
	$(E) "Run 'make' to build the Linux ext2fs kernel module."
	$(E) ""
	$(E) "Please run 'make <target>' where target is one of the following:"
	$(E) "* linux"
	$(E) "  Build the Linux kernel module(default)."
	$(E) "  This will build against the kernel headers of the current running kernel."
	$(E) "  Pass KERNELDIR=<path-to-kernel-headers> if you want to build against a different kernel version."
	$(E) "  eg.:"
	$(E) "     make linux"
	$(E) "     make linux KERNELDIR=/usr/src/linux-headers-4.3.0-1-amd64/"
	$(E) ""
	$(E) "* debug"
	$(E) "  Build the Linux kernel module with debugging enabled."
	$(E) "  This is equivalent to running 'make linux DEBUG=1'"
	$(E) ""
	$(E) "* verification"
	$(E) "  Generate verification table."
	$(E) ""
	$(E) "* clean"
	$(E) "  Cleanup."
	$(E) ""
	$(E) "* help"
	$(E) "  Print this help."
endif
