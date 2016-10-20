#
# Copyright 2016, NICTA
#
# This software may be distributed and modified according to the terms of
# the GNU General Public License version 2. Note that NO WARRANTY is provided.
# See "LICENSE_GPLv2.txt" for details.
#
# @TAG(NICTA_GPL)
#

#
# Makefile for the BilbyFs module (bilbyfs.ko)
#

# Run `make OS=linux' or `make OS=sel4' or
# export OS environment variable
OS=linux

# Comment/uncomment the following line to disable/enable debugging
DEBUG = n

OS_PATH=os/$(OS)
EXTRA_CFLAGS += -I$(PWD) -I$(PWD)/$(OS_PATH) -fstack-usage

ifeq ($(DEBUG),y)
  EXTRA_CFLAGS += -g -DBILBYFS_DEBUG
endif

# Linux kernel build system requires that there is no .c file named
# after the name of the resulting .ko file.
# In our case we are not allowed to have a "bilbyfs.c" file
#
MODULE = bilbyfs

ifeq ($(OS),linux)
  OS_SPEC_FILES = $(OS_PATH)/wrapper.o
endif

ifeq ($(OS),sel4)
  OS_SPEC_FILES = $(OS_PATH)/wrapper.o $(OS_PATH)/ubisim.o
endif

# call from kernel build system
ifneq ($(KERNELRELEASE),)

  obj-m	+= $(MODULE).o
  $(MODULE)-objs := \
	$(OS_SPEC_FILES) \
	fsop.o \
	packobj.o \
	ostore.o \
	wbuf.o \
	rdx.o \
	dentarr.o \
	fsm.o \
	idx.o \
	rbt.o \
	gim.o \
	gc.o \
	allocpool.o \
	debug.o

else

  KERNELDIR ?= /lib/modules/$(shell uname -r)/build
  PWD       := $(shell pwd)

default:
	$(MAKE) CFLAGS="$(CFLAGS) $(EXTRA_CFLAGS)" -C $(KERNELDIR) M=$(PWD) modules
clean:
	$(MAKE) -C $(KERNELDIR) M=$(PWD) clean

endif

