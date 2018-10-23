#
# Copyright 2016, NICTA
#
# This software may be distributed and modified according to the terms of
# the GNU General Public License version 2. Note that NO WARRANTY is provided.
# See "LICENSE_GPLv2.txt" for details.
#
# @TAG(NICTA_GPL)
#

ROOT_DIR=../../../../../

include $(ROOT_DIR)build-env.mk

OUTPUT=readpage
SRC=readpage.cogent

STDGUM=$(COGENT_STD_GUM_DIR)
ifeq ($(STDGUM),)
STDGUM=$(shell cogent --stdgum-dir)
endif

# COGENT flags
COGENT_FLAGS+= -Od --fno-static-inline --fno-fncall-as-macro --fnormalisation=knf --ffunc-purity-attr
# end of configuration

PWD:= $(shell pwd)
override COGENT_FLAGS+=  \
			--root-dir=$(ROOT_DIR) \
			--abs-type-dir=$(PWD)

DIST_DIR = .

.PHONY: default hs

default: hs
all: hs

hs:
	$(Q)cogent $(SRC) --hs-shallow-desugar-tuples $(COGENT_FLAGS) \
                    --dist-dir=$(DIST_DIR)
