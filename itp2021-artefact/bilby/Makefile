#
# Copyright 2016, NICTA
#
# This software may be distributed and modified according to the terms of
# the GNU General Public License version 2. Note that NO WARRANTY is provided.
# See "LICENSE_GPLv2.txt" for details.
#
# @TAG(NICTA_GPL)
#

#include ../../../../build-env.mk

#COGENT_FLAGS ?=

all: 
	L4V_ARCH=ARM isabelle build -v -d . -d ../cogent -d ../cogent/autocorres -b BilbyFs
#
#cogent:
#	cogent --shallow-consts-desugar-tuples --shallow-desugar-tuples --proof-name=BilbyFs \
#				--dist-dir="impl" --root-dir="$(BUILD_ENV_MK_DIR)" $(COGENT_FLAGS) \
#				../cogent/src/fsop.cogent
sync: 
	L4V_ARCH=ARM isabelle build -v -d . -d ../cogent -d ../cogent/autocorres -b BilbyFsSync

iget: 
	L4V_ARCH=ARM isabelle build -v -d . -d ../cogent -d ../cogent/autocorres -b BilbyFsIget
