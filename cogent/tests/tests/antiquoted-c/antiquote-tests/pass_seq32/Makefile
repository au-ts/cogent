#
# Copyright 2016, NICTA
#
# This software may be distributed and modified according to the terms of
# the GNU General Public License version 2. Note that NO WARRANTY is provided.
# See "LICENSE_GPLv2.txt" for details.
#
# @TAG(NICTA_GPL)
#

NAME=seq32_sum

SRC=seq32_sum.cogent
OUTPUT=generated # $(SRC:.cogent=-gen)
COUTPUT=$(addsuffix .c, $(OUTPUT))
HOUTPUT=$(addsuffix .h, $(OUTPUT))

LIBGUM=$(shell cogent --libgum-dir)

AHFILES=
ACFILES=main.ac

PP=$(ACFILES:.ac=_pp.ac)
PPINFER=$(ACFILES:.ac=_pp_inferred.c)

ABSDIR=./abstract

OBJ=$(ACFILES:.ac=_pp_inferred.o)

CFLAGS+=-I. -I$(LIBGUM) -std=gnu99

.PHONY: default cogent clean gen-anti test
.SECONDARY:

default: all

all: gen-anti $(OBJ)
	$(CC) -o $(NAME) $(OBJ)

test: gen-anti $(OBJ)

%c:
	$(CC) -c $< -o $@

gen-anti-prune:
	mkdir -p $(ABSDIR)
	cogent -g $(SRC) --infer-c-types="$(AHFILES)" --infer-c-funcs="$(ACFILES)" \
		    --cpp="$(CPP)" \
				--cpp-args="-x c \$$CPPIN -o \$$CPPOUT -E -P $(CFLAGS)" \
				--entry-funcs=entrypoints.cfg --prune-call-graph=entrypoints.cfg \
				-ogenerated

gen-anti:
	mkdir -p $(ABSDIR)
	cogent -g $(SRC) --infer-c-types="$(AHFILES)" --infer-c-funcs="$(ACFILES)" \
		    --cpp="$(CPP)" \
				--cpp-args="-x c \$$CPPIN -o \$$CPPOUT -E -P $(CFLAGS)" \
				--entry-funcs=entrypoints.cfg --prune-call-graph=entrypoints.cfg \
				-ogenerated


clean:
	rm -f $(COUTPUT) $(HOUTPUT) $(PP) $(PPINFER) $(OBJ)
	@# rm -f *-gen.*
	rm -rf $(ABSDIR)
	rm -f $(NAME)

