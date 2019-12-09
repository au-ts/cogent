# You need to set COGENT_ROOT and AC_DIR, if different from the default.

NAME=Trivial
SRC=$(NAME).cogent

ifndef COGENT_ROOT
COGENT_ROOT=../../../
endif

ifndef AC_DIR
AC_DIR=$(COGENT_ROOT)/autocorres
endif


COGENT_FLAGS= -A \
              -Od --fno-static-inline --fno-fncall-as-macro --ffunc-purity-attr \
							--root-dir=$(COGENT_ROOT) \
							--dist-dir=build/ \
							--fake-header-dir=$(COGENT_ROOT)/cogent/lib

.PHONY: default gen-c-proof verif clean 

default: gen-c-proof

gen-c-proof:
	cogent $(SRC) $(COGENT_FLAGS)

verif: gen-c-proof
	L4V_ARCH=ARM isabelle build -d ./build -d $(COGENT_ROOT)/cogent/isa -d $(AC_DIR) -v -b $(NAME)_AllRefine

clean:
	rm -rf build
