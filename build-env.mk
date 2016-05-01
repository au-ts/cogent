#
# Copyright 2016, NICTA
#
# This software may be distributed and modified according to the terms of
# the GNU General Public License version 2. Note that NO WARRANTY is provided.
# See "LICENSE_GPLv2.txt" for details.
#
# @TAG(NICTA_GPL)
#

# Common environment variables for makefiles.
# See “build-env.sh” for more information.
#
# Note that this file sets the PATH, so it should be included before any
# makefile directives that change the PATH.

SHELL:=bash

BUILD_ENV_MK_DIR:=$(dir $(lastword $(MAKEFILE_LIST)))

# TODO: more efficient way to do this?
L4V_DIR:=$(shell source "$(BUILD_ENV_MK_DIR)"/build-env.sh; echo "$$L4V_DIR")
ISABELLE:=$(shell source "$(BUILD_ENV_MK_DIR)"/build-env.sh; echo "$$ISABELLE")
ISABELLE_BUILD:=$(shell source "$(BUILD_ENV_MK_DIR)"/build-env.sh; echo "$$ISABELLE_BUILD")

export PATH:=$(shell source "$(BUILD_ENV_MK_DIR)"/build-env.sh; echo "$$PATH")

