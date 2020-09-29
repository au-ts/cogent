NAME=SPI

SRC=SPI.cogent
OUTPUT=spi # $(SRC:.cogent=-gen)
COUTPUT=$(addsuffix .c, $(OUTPUT))
HOUTPUT=$(addsuffix .h, $(OUTPUT))

LIBGUM=$(shell cogent --libgum-dir)
AHFILES=$(LIBGUM)gum/anti/abstract/WordArray.ah
ACFILES=spi.ac

PP=$(ACFILES:.ac=_pp.ac)
PPINFER=$(ACFILES:.ac=_pp_inferred.c)

ABSDIR=./abstract

OBJ=$(PPINFER:.c=.o)

CFLAGS+=-I. -I$(LIBGUM) -I$(LIBGUM)gum/anti -std=gnu99

.PHONY: default cogent clean
.SECONDARY:

default: all

all:
	mkdir -p $(ABSDIR)
	cogent -g -o generated --infer-c-types="$(AHFILES)" \
		--ext-types=types.cfg \
		--Wno-warn --infer-c-funcs="$(ACFILES)" \
		--cpp-args="\$$CPPIN -o \$$CPPOUT -E -P $(CFLAGS)" \
		--entry-funcs=entrypoints.cfg $(SRC)

clean:
	rm -rf $(ABSDIR) generated.{c,h} spi_pp.ac spi_pp_inferred.c
