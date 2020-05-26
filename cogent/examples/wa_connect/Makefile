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

SRC=WordArray.cogent
OUTPUT=WordArray # $(SRC:.cogent=-gen)
COUTPUT=$(addsuffix .c, $(OUTPUT))
HOUTPUT=$(addsuffix .h, $(OUTPUT))

STDGUM=$(shell cogent --stdgum-dir)

AHFILES=$(STDGUM)/gum/anti/abstract/WordArray.ah
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
	cogent -C -g -Od -ogenerated \
		--infer-c-types="$(AHFILES)" \
		--Wno-warn --infer-c-funcs="$(ACFILES)" \
		--cpp-args="\$$CPPIN -o \$$CPPOUT -E -P $(CFLAGS)" \
		--proof-input-c=$(PPINFER) \
		--entry-funcs=entrypoints.cfg $(SRC)
	cp generated.table main_pp_inferred.table

clean:
	rm -r $(ABSDIR) ROOT generated* BUILD_INFO main_pp* Generated*
