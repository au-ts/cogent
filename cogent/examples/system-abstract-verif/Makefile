#
# Copyright 2017, NICTA
#
# This software may be distributed and modified according to the terms of
# the GNU General Public License version 2. Note that NO WARRANTY is provided.
# See "LICENSE_GPLv2.txt" for details.
#
# @TAG(NICTA_GPL)
#

# The name of our source file
NAME=Kernel

# Location of the Cogent repository
REPO="../../.."

# Our input source file, output targets
SRC=Kernel.cogent
OUTPUT=Kernel # $(SRC:.cogent=-gen)
COUTPUT=$(addsuffix .c, $(OUTPUT))
HOUTPUT=$(addsuffix .h, $(OUTPUT))

# Location of Cogent stdlib
STDGUM=$(shell cogent --stdgum-dir)

# The wrapper files for compiling our system/verification
SYSTEM_ACFILES=plat/system/wrapper.ac
VERIF_ACFILES=plat/verification/wrapper.ac

# Compile with the right file depending on what we want to build
system: ACFILES=$(SYSTEM_ACFILES)
verification: ACFILES=$(VERIF_ACFILES)
clean: ACFILES=$(VERIF_ACFILES) $(SYSTEM_ACFILES)

# Preprocessed and inferred antiquoted C files
PP=$(ACFILES:.ac=_pp.ac)
PPINFER=$(ACFILES:.ac=_pp_inferred.c)

# Compilation objects
OBJ=$(PPINFER:.c=.o)

# Extra flags for the C compiler
CFLAGS=-I. -I$(STDGUM) -I$(STDGUM)/gum/anti -std=gnu99

.PHONY: default clean system verification
.SECONDARY:

all: $(OBJ) system

# Build all our objects
$(OBJ): $(PPINFER)

system: $(OBJ)
	# Compile the Cogent source
	cogent $(SRC) -g -o$(OUTPUT) \
		--dist-dir=plat/system \
		--root-dir="$(REPO)" \
		--Wno-warn --infer-c-funcs="$(SYSTEM_ACFILES)" \
		--cpp-args="\$$CPPIN -o \$$CPPOUT -P $(CFLAGS)" \
		--ext-types=types.cfg \
		--entry-funcs=entrypoints.cfg

    # Compile the C code
	$(CC) -o $(NAME) $(OBJ)

verification:
	# Compile cogent source and build all verification files
	cogent $(SRC) -g -o$(OUTPUT) \
		--dist-dir=plat/verification \
		--root-dir="$(REPO)" \
		--Wno-warn --infer-c-funcs="$(VERIF_ACFILES)" \
		--cpp-args="\$$CPPIN -o \$$CPPOUT -P $(CFLAGS)" \
		--ext-types=types.cfg \
		--entry-funcs=entrypoints.cfg \
		--proof-input-c=wrapper_pp_inferred.c \
		-A

clean:
	rm -f plat/system/$(COUTPUT) plat/system/$(HOUTPUT) plat/system/$(PP) plat/system/$(PPINFER) plat/system/$(OBJ)
	rm -f plat/verification/$(COUTPUT) plat/verification/$(HOUTPUT) plat/verification/$(PP) plat/verification/$(PPINFER) plat/verification/$(OBJ)
	@# rm -f *-gen.*
	rm -f plat/verification/$(NAME)_*.thy
	rm -rf $(NAME)
	rm -f plat/verification/ROOT
	rm -f plat/verification/Kernel.table
	rm -f plat/verification/BUILD_INFO
	rm -f plat/system/BUILD_INFO
