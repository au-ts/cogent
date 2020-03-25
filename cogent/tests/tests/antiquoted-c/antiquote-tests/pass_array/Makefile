#
# Copyright 2016, NICTA
#
# This software may be distributed and modified according to the terms of
# the GNU General Public License version 2. Note that NO WARRANTY is provided.
# See "LICENSE_GPLv2.txt" for details.
#
# @TAG(NICTA_GPL)
#

NAME=array_simple

SRC=array_simple.cogent
OUTPUT=generated # $(SRC:.cogent=-gen)
COUTPUT=$(addsuffix .c, $(OUTPUT))
HOUTPUT=$(addsuffix .h, $(OUTPUT))

STDGUM=$(shell cogent --stdgum-dir)

AHFILES=$(STDGUM)/gum/anti/abstract/Array.ah
ACFILES=main.ac

PP=$(ACFILES:.ac=_pp.ac)
PPINFER=$(ACFILES:.ac=_pp_inferred.c)

ABSDIR=./abstract

OBJ=$(PPINFER:.c=.o)

CFLAGS+=-I. -I$(STDGUM) -std=gnu99

.PHONY: default cogent clean gen-anti test
.SECONDARY:

default: all

all: gen-anti $(OBJ)
	$(CC) -o $(NAME) $(OBJ)

test: gen-anti $(OBJ)

$(OBJ): $(PPINFER)

gen-anti:
	mkdir -p $(ABSDIR)
	cogent $(SRC) -g -Od -ogenerated --fno-fncall-as-macro --ffunc-purity-attr \
		--infer-c-types="$(AHFILES)" \
		--Wno-warn --infer-c-funcs="$(ACFILES)" \
		--cpp-args="\$$CPPIN -o \$$CPPOUT -E -P $(CFLAGS)" \
		--ext-types=types.cfg \
		--entry-funcs=entrypoints.cfg \
		--cogent-pp-args="--noline"

clean:
	rm -f $(COUTPUT) $(HOUTPUT) $(PP) $(PPINFER) $(OBJ)
	@# rm -f *-gen.*
	rm -rf $(ABSDIR)
	rm -f $(NAME)

