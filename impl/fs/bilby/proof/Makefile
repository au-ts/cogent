#
# Copyright 2016, NICTA
#
# This software may be distributed and modified according to the terms of
# the GNU General Public License version 2. Note that NO WARRANTY is provided.
# See "LICENSE_GPLv2.txt" for details.
#
# @TAG(NICTA_GPL)
#

include ../../../../build-env.mk

COGENT_FLAGS ?=

all: cogent
	L4V_ARCH=$(L4V_ARCH) $(ISABELLE) build -v -d . -d $(BUILD_ENV_MK_DIR) -d $(AC_DIR) -b BilbyFs

cogent:
	cogent --shallow-consts-desugar-tuples --shallow-desugar-tuples --proof-name=BilbyFs \
				--dist-dir="impl" --root-dir="$(BUILD_ENV_MK_DIR)" $(COGENT_FLAGS) \
				../cogent/src/fsop.cogent
sync: cogent
	L4V_ARCH=$(L4V_ARCH) $(ISABELLE) build -v -d . -d $(AC_DIR) -d $(BUILD_ENV_MK_DIR) -b BilbyFsSync

iget: cogent
	L4V_ARCH=$(L4V_ARCH) $(ISABELLE) build -v -d . -d $(AC_DIR) -d $(BUILD_ENV_MK_DIR) -b BilbyFsIget
