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
	$(ISABELLE) build -v -d . -b BilbyFs

cogent:
	cogent-2.0.8.1 --shallow-consts-desugar-tuples --shallow-desugar-tuples --proof-name=BilbyFs \
				--dist-dir="impl" --root-dir="$(BUILD_ENV_MK_DIR)" $(COGENT_FLAGS) \
				../cogent/src/fsop.cogent
sync: cogent
	$(ISABELLE) build -v -d . -b BilbyFsSync

iget: cogent
	$(ISABELLE) build -v -d . -b BilbyFsIget
