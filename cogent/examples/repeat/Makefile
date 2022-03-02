NAME=test

SRC=test.cogent
OUTPUT=test
COUTPUT=$(addsuffix .c, $(OUTPUT))
HOUTPUT=$(addsuffix .h, $(OUTPUT))

AHFILES=WordArray.ah

ACFILES=main.ac

LIBGUM=$(shell cogent --libgum-dir)

PP=$(ACFILES:.ac=_pp.ac)
PPINFER=$(ACFILES:.ac=_pp_inferred.c)

OBJ=$(PPINFER:.c=.o)

CFLAGS+=-I. -I$(LIBGUM) -I$(BUILDDIR) -std=gnu99

BUILDDIR=build
ABSDIR=abstract

.PHONY: default cogent clean gen-anti test
.SECONDARY:

default: all

all:
	mkdir -p $(BUILDDIR)
	mkdir -p "$(BUILDDIR)/$(ABSDIR)"
	cogent -g -Od -ogenerated \
		--infer-c-types="$(AHFILES)" \
		--abs-type-dir="$(BUILDDIR)" \
		--Wno-warn --infer-c-funcs="$(ACFILES)" \
		--cpp-args="\$$CPPIN -o \$$CPPOUT -E -P $(CFLAGS)" \
		--proof-input-c=$(PPINFER) \
	    --dist-dir=$(BUILDDIR) \
		--entry-funcs=entrypoints.cfg $(SRC) 

clean:
	rm -r $(BUILDDIR)
