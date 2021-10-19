
NAME=bitfields

SRC=bitfields.cogent

LIBGUM=$(shell cogent --libgum-dir)

ACFILES=main.ac

PP=$(ACFILES:.ac=_pp.ac)
PPINFER=$(ACFILES:.ac=_pp_inferred.c)

ABSDIR=./abstract

OBJ=$(PPINFER:.c=.o)

CFLAGS+=-I. -I$(LIBGUM) -I$(LIBGUM)/gum/anti -std=gnu99

.PHONY: default clean gen-anti test manual
.SECONDARY:

default: all

all: gen-anti $(OBJ)
	$(CC) -o $(NAME) $(OBJ)

test: gen-anti $(OBJ)

$(OBJ): $(PPINFER)

gen-anti:
	mkdir -p $(ABSDIR)
	cogent $(SRC) -g -Od -ogenerated --fno-fncall-as-macro --ffunc-purity-attr \
                --infer-c-funcs="$(ACFILES)" \
                --cpp-args="\$$CPPIN -o \$$CPPOUT -E -P $(CFLAGS)" \
                --entry-funcs=entry.cfg \

manual:
	$(CC) main.c -I$(LIBGUM) -o bitfields-manual

clean:
	rm -f $(COUTPUT) $(HOUTPUT) $(PP) $(PPINFER) $(OBJ)
	rm -rf generated.h generated.c
	rm -f $(ABSDIR)/*.h
	rm -rf $(ABSDIR)
	rm -f $(NAME)
	rm -f bitfields-manual
