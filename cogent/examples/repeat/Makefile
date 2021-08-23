NAME=test

SRC=test.cogent
OUTPUT=test
COUTPUT=$(addsuffix .c, $(OUTPUT))
HOUTPUT=$(addsuffix .h, $(OUTPUT))

ACFILES=main.ac

LIBGUM=$(shell cogent --libgum-dir)

PP=$(ACFILES:.ac=_pp.ac)
PPINFER=$(ACFILES:.ac=_pp_inferred.c)

OBJ=$(PPINFER:.c=.o)

CFLAGS+=-I. -I$(LIBGUM) -std=gnu99

BUILDDIR=build

.PHONY: default cogent clean gen-anti test
.SECONDARY:

default: all

all:
	mkdir -p $(BUILDDIR)
	cogent -A -g -Od -ogenerated \
		--Wno-warn --infer-c-funcs="$(ACFILES)" \
		--cpp-args="\$$CPPIN -o \$$CPPOUT -E -P $(CFLAGS)" \
		--proof-input-c=$(PPINFER) \
	    --dist-dir=$(BUILDDIR) \
		--entry-funcs=entrypoints.cfg $(SRC) 
	cp build/generated.table build/main_pp_inferred.table

clean:
	rm -r $(BUILDDIR)
