#
# Copyright 2019, NICTA
#
# This software may be distributed and modified according to the terms of
# the GNU General Public License version 2. Note that NO WARRANTY is provided.
# See "LICENSE_GPLv2.txt" for details.
#
# @TAG(NICTA_GPL)
#

NAME=bag

SRC=Bag.cogent
OUTPUT=generated # $(SRC:.cogent=-gen)
COUTPUT=$(addsuffix .c, $(OUTPUT))
HOUTPUT=$(addsuffix .h, $(OUTPUT))

STDGUM=$(shell cogent --stdgum-dir)
AHFILES=List.ah
ACFILES=main.ac

PP=$(ACFILES:.ac=_pp.ac)
PPINFER=$(ACFILES:.ac=_pp_inferred.c)

ABSDIR=./abstract

OBJ=$(PPINFER:.c=.o)

CFLAGS+=-I. -I$(STDGUM) -std=gnu99

.PHONY: default mk-c clean
.SECONDARY:

default: all

all: mk-c $(OBJ)
	$(CC) -o $(NAME) $(OBJ)

$(OBJ): $(PPINFER)

mk-c:
	mkdir -p $(ABSDIR)
	cogent $(SRC) -g -Od -ogenerated --fno-fncall-as-macro --ffunc-purity-attr \
		--infer-c-types="$(AHFILES)" \
		--Wno-warn --infer-c-funcs="$(ACFILES)" \
		--cpp="$(CPP)" \
		--cpp-args="-x c -P \$$CPPIN -o \$$CPPOUT $(CFLAGS)" \
		--ext-types=types.cfg \
		--entry-funcs=entrypoints.cfg

clean:
	rm -f $(COUTPUT) $(HOUTPUT) $(PP) $(PPINFER) $(OBJ)
	@# rm -f *-gen.*
	rm -f $(ABSDIR)/*.h
	rm -f $(NAME)
