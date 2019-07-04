#
# Copyright 2016, NICTA
#
# This software may be distributed and modified according to the terms of
# the GNU General Public License version 2. Note that NO WARRANTY is provided.
# See "LICENSE_GPLv2.txt" for details.
#
# @TAG(NICTA_GPL)
#

NAME=iterator_sum

SRC=iterator_sum.cogent
OUTPUT=generated # $(SRC:.cogent=-gen)
COUTPUT=$(addsuffix .c, $(OUTPUT))
HOUTPUT=$(addsuffix .h, $(OUTPUT))

STDGUM=$(shell cogent --stdgum-dir)

AHFILES=
ACFILES=main.ac

PP=$(ACFILES:.ac=_pp.ac)
PPINFER=$(ACFILES:.ac=_pp_inferred.c)

ABSDIR=./abstract

OBJ=$(ACFILES:.ac=_pp_inferred.o)

CFLAGS+=-I. -I$(STDGUM) -std=gnu99

.PHONY: default cogent clean gen-anti test
.SECONDARY:

default: all

all: gen-anti $(OBJ)
	$(CC) -o $(NAME) $(OBJ)

test: gen-anti $(OBJ)

%c:
	$(CC) -c $< -o $@

gen-anti:
	mkdir -p $(ABSDIR)
	cogent -g $(SRC) --infer-c-types="$(AHFILES)" --infer-c-funcs="$(ACFILES)" --cpp-args="\$$CPPIN -o \$$CPPOUT -E -P $(CFLAGS)" --ext-types=types.cfg -O1 -ogenerated

clean:
	rm -f $(COUTPUT) $(HOUTPUT) $(PP) $(PPINFER) $(OBJ)
	@# rm -f *-gen.*
	rm -rf $(ABSDIR)
	rm -f $(NAME)

