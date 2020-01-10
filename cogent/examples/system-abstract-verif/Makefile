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
OUTPUT=kernel # $(SRC:.cogent=-gen)
COUTPUT=$(addsuffix .c, $(OUTPUT))
HOUTPUT=$(addsuffix .h, $(OUTPUT))

# Location of Cogent stdlib
STDGUM=$(shell cogent --stdgum-dir)

# The wrapper files for compiling our system/verification
SYSTEM_ACFILES=plat/system/wrapper.ac
VERIF_ACFILES=plat/verification/wrapper.ac

# Compile with the right wrapper file depending on what we want to build
ifeq ($(findstring system,${MAKECMDGOALS}),system)
  ACFILES := ${SYSTEM_ACFILES}
else
  ifeq ($(findstring verification,${MAKECMDGOALS}),verification)
    ACFILES := ${VERIF_ACFILES}
  else
    ifeq ($(findstring clean,${MAKECMDGOALS}),clean)
      ACFILES := ${SYSTEM_ACFILES} ${VERIF_ACFILES}
	else
      $(error Must compile either 'system' or 'verification' targets.)
    endif
  endif
endif

# Preprocessed and inferred antiquoted C files
PP      := $(ACFILES:.ac=_pp.ac)
PPINFER := $(ACFILES:.ac=_pp_inferred.c)

# Compilation objects
OBJ     := $(PPINFER:.c=.o)

# Extra flags for the C compiler
CFLAGS=-I. -I$(STDGUM) -I$(STDGUM)/gum/anti -std=gnu99

# Common flags for the cogent compiler
COGENT_FLAGS=--Wno-warn \
			 --root-dir="$(REPO)" \
			 --cpp-args="\$$CPPIN -o \$$CPPOUT -P $(CFLAGS)" \
			 --ext-types=types.cfg \
			 --entry-funcs=entrypoints.cfg

.PHONY: clean # system verification

# Compile the actual code for running
system: .system ${OBJ}
	$(CC) -o $(OUTPUT) ${OBJ}

${OBJ}: ${PPINFER}
${PPINFER}: .system
.system:
	# Compile the Cogent source
	cogent $(SRC) -g -o$(OUTPUT) \
		$(COGENT_FLAGS) \
		--dist-dir=plat/system \
		--infer-c-funcs="$(SYSTEM_ACFILES)" 

# Compile cogent source and generate all verification files
verification:
	cogent $(SRC) -g -o$(OUTPUT) \
		$(COGENT_FLAGS) \
		--dist-dir=plat/verification \
		--infer-c-funcs="$(VERIF_ACFILES)" \
		--proof-input-c=wrapper_pp_inferred.c \
		-A

clean:
	rm -f plat/system/$(COUTPUT) plat/system/$(HOUTPUT)
	rm -f plat/verification/$(COUTPUT) plat/verification/$(HOUTPUT)
	rm -f $(PP) $(PPINFER) $(OBJ)
	rm -f plat/verification/$(NAME)_*.thy
	rm -f $(OUTPUT)
	rm -f plat/verification/ROOT
	rm -f plat/verification/kernel.table
	rm -f plat/verification/BUILD_INFO
	rm -f plat/system/BUILD_INFO
