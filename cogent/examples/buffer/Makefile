#
# Copyright 2021, Trustworthy Systems Group (UNSW)
#
# This software may be distributed and modified according to the terms
# of the GNU General Public License version 2. Note that NO WARRANTY is
# provided.	 See "LICENSE_GPLv2.txt" for details.
#
# @TAG(UNSW_GPL)
#

DIR:=brutal objects writable
MKS:=$(patsubst %, %-mk, $(DIR))
RMS:=$(patsubst %, %-rm, $(DIR))

all: $(MKS)

.PHONY: all clean

%-mk: %
	make -C $<

%-rm: %
	make clean -C $<

clean: $(RMS)
