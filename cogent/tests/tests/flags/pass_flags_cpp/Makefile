#
# Copyright 2016, NICTA
#
# This software may be distributed and modified according to the terms of
# the GNU General Public License version 2. Note that NO WARRANTY is provided.
# See "LICENSE_GPLv2.txt" for details.
#
# @TAG(NICTA_GPL)
#


SRC=cpp.cogent
OUTPUT=generated # $(SRC:.cogent=-gen)
COUTPUT=$(addsuffix .c, $(OUTPUT))
HOUTPUT=$(addsuffix .h, $(OUTPUT))

.PHONY: default test clean 

default: test

test:
	cogent $(SRC) -g -Od -o$(OUTPUT) --fno-fncall-as-macro --ffunc-purity-attr \
		--cogent-pp-args="$(CPPFLAGS)"

clean:
	rm -f $(COUTPUT) $(HOUTPUT)
