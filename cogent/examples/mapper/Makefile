#
# Copyright 2017, NICTA
#
# This software may be distributed and modified according to the terms of
# the GNU General Public License version 2. Note that NO WARRANTY is provided.
# See "LICENSE_GPLv2.txt" for details.
#
# @TAG(NICTA_GPL)
#

NAME=mapper

SRC=Mapper.cogent
OUTPUT=$(NAME)
COUTPUT=$(addsuffix .c, $(OUTPUT))
HOUTPUT=$(addsuffix .h, $(OUTPUT))

LIBGUM=$(shell cogent --libgum-dir)

AHFILES=$(LIBGUM)gum/anti/abstract/WordArray.ah \
				$(LIBGUM)gum/anti/abstract/View.ah
ACFILES=main.ac

PP=$(ACFILES:.ac=_pp.ac)
PPINFER=$(ACFILES:.ac=_pp_inferred.c)

ABSDIR=./

OBJ=$(PPINFER:.c=.o)

CFLAGS+=-I. -I$(LIBGUM) -I$(LIBGUM)/gum/anti -std=gnu99

.PHONY: default clean gen-anti
.SECONDARY:

default: all

all: gen-anti $(OBJ)
	$(CC) -o $(NAME) $(OBJ)

$(OBJ): $(PPINFER)

gen-anti:
	mkdir -p $(ABSDIR)
	cogent $(SRC) -g -o$(OUTPUT) \
		--abs-type-dir="$(ABSDIR)" \
		--infer-c-types="$(AHFILES)" \
		--infer-c-funcs="$(ACFILES)" \
		--cpp="$(CPP)" \
		--cpp-args="-x c \$$CPPIN -o \$$CPPOUT -E -P $(CFLAGS)" \
		--entry-funcs=entrypoints.cfg

clean:
	rm -f $(COUTPUT) $(HOUTPUT) $(PP) $(PPINFER) $(OBJ)
	@# rm -f *-gen.*
	rm -f $(ABSDIR)/*.h
	rm -f $(NME)
