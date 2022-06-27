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
NAME=main

# Location of the Cogent repository
REPO=../../..

# Our input source file, output targets
SRC=$(NAME).cogent
OUTPUT=cogent_main
COUTPUT=$(addsuffix .c, $(OUTPUT))
HOUTPUT=$(addsuffix .h, $(OUTPUT))

# Location of output files
BUILD_DIR=build

# Location of Cogent stdlib
LIBGUM=$(shell cogent --libgum-dir)

ACFILES = main.ac # $(LIBGUM)/lib/anti/common.ac $(LIBGUM)/lib/anti/recursive_list.ac

# Preprocessed and inferred antiquoted C files
PP      = $(ACFILES:.ac=_pp.ac)
PPINFER = $(ACFILES:.ac=_pp_inferred.c)

# Compilation objects
OBJ     = $(PPINFER:.c=.o)

# Extra flags for the C compiler
CFLAGS=-I. -I$(LIBGUM) -I$(LIBGUM)/gum/anti -std=gnu99 -I$(BUILD_DIR)

# Common flags for the cogent compiler
COGENT_FLAGS=--Wno-warn \
			 --root-dir="$(REPO)" \
			 --dist-dir=$(BUILD_DIR) \
			 --cpp="$(CPP)" \
			 --cpp-args="-x c \$$CPPIN -o \$$CPPOUT -P $(CFLAGS)" \

.PHONY: default all clean main

default: all

all: main 

# Compile the actual code for running
main: $(BUILD_DIR)/${OBJ} .main
	$(CC) -o $(OUTPUT) $<

$(BUILD_DIR)/$(OBJ): .main
	$(CC) -c -o $@ $(BUILD_DIR)/$(PPINFER)  $(CFLAGS)

.main:
	mkdir -p $(BUILD_DIR)
	# Compile the Cogent source
	cogent $(SRC) -g -o$(OUTPUT) \
		$(COGENT_FLAGS) \
		--infer-c-funcs="$(ACFILES)" 

clean:
	rm -rf $(BUILD_DIR)
	rm -rf $(OUTPUT)
