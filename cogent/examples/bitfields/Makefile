NAME=test

SRC=test.cogent
OUTPUT=test
COUTPUT=$(addsuffix .c, $(OUTPUT))
HOUTPUT=$(addsuffix .h, $(OUTPUT))

AHFILES=

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
	cp main.ac main.ac.bak
	sed -i "s#build/generated.c#$(BUILDDIR)/generated.c#" main.ac
	cogent -A -g -Od -ogenerated \
		--abs-type-dir="$(BUILDDIR)" \
		--Wno-warn --infer-c-funcs="$(ACFILES)" \
		--cpp-args="\$$CPPIN -o \$$CPPOUT -E -P $(CFLAGS)" \
		--proof-input-c=$(PPINFER) \
	    --dist-dir=$(BUILDDIR) \
		--entry-funcs=entrypoints.cfg $(SRC)  \
		--funused-dargent-accessors
		#--infer-c-types="$(AHFILES)" 
	cp $(BUILDDIR)/generated.table $(BUILDDIR)/main_pp_inferred.table
	sed -i "s/^typedecl \+U2/type_synonym U2 = \"2 word\"/" "$(BUILDDIR)/Generated_ShallowShared.thy"
	sed -i "s/^typedecl \+U4/type_synonym U4 = \"4 word\"/" "$(BUILDDIR)/Generated_ShallowShared.thy"
	mv main.ac.bak main.ac
	python3 repl.py $(BUILDDIR)
	python3 fixgetset.py $(BUILDDIR)

clean:
	rm -r $(BUILDDIR)
	mv main.ac.bak main.ac
