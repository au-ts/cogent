# 
#  Copyright 2019, Data61
#  Commonwealth Scientific and Industrial Research Organisation (CSIRO)
#  ABN 41 687 119 230.
# 
#  This software may be distributed and modified according to the terms of
#  the GNU General Public License version 2. Note that NO WARRANTY is provided.
#  See "LICENSE_GPLv2.txt" for details.
# 
#  @TAG(DATA61_GPL)
# 

NAME=swap-drop

SRC=SwapDrop.cogent
OUTPUT=$(NAME)
COUTPUT=$(addsuffix .c, $(OUTPUT))
HOUTPUT=$(addsuffix .h, $(OUTPUT))

LIBGUM=$(shell cogent --libgum-dir)

ACFILES=main.ac

PP=$(ACFILES:.ac=_pp.ac)
PPINFER=$(ACFILES:.ac=_pp_inferred.c)

OBJ=$(PPINFER:.c=.o)

CFLAGS=-I. -I$(LIBGUM) -std=c99

.PHONY: default clean gen-anti
.SECONDARY:

default: all

all: gen-anti $(OBJ)
	$(CC) -o $(NAME) $(OBJ)

$(OBJ): $(PPINFER)

gen-anti:
	cogent $(SRC) -g -o$(OUTPUT) \
		--Wno-warn --infer-c-funcs="$(ACFILES)" \
		--cpp="$(CPP)" \
		--cpp-args="\$$CPPIN -o \$$CPPOUT -P $(CFLAGS)" \
		--entry-funcs=entrypoints.cfg

clean:
	rm -f $(COUTPUT) $(HOUTPUT) $(PP) $(PPINFER) $(OBJ)
	@# rm -f *-gen.*
	rm -f $(NAME)
	rm -f *.thy
	rm -f ROOT
	rm -f BUILD_INFO
