#!/bin/sh
#
# Copyright 2016, NICTA
#
# This software may be distributed and modified according to the terms of
# the GNU General Public License version 2. Note that NO WARRANTY is provided.
# See "LICENSE_GPLv2.txt" for details.
#
# @TAG(NICTA_GPL)
#

# Common environment variables.
# All build scripts should “source” this file. For makefiles, use “build-env.mk” instead.
#
# Variables:
#   L4V_DIR: location of l4.verified directory (https://github.com/NICTA/l4v).
#            l4.v is a dependency of proof builds.
#
# Extra PATH variables:
#   ISABELLE_TOOLDIR: location of “isabelle” theorem prover.
#                     Defaults to L4V_DIR/isabelle/bin.
#
#   COGENT_TOOLDIR: location of “cogent” compiler.
#
# These will be added to the PATH if not already present.
#
# If any variable has already been defined, it will be left alone.

find_script_dir() {
   (
       while test "$PWD" != '/' -a ! -f build-env.mk
       do
	  cd ..
       done
       echo "$PWD"
   )
}

set_build_env()
{
  
  local SCRIPT_DIR=`find_script_dir`
  : ${AC_DIR:="$SCRIPT_DIR/autocorres"}
  : ${L4V_ARCH:="ARM"}

  # Location of Isabelle (sub-module)
  : ${ISABELLE_TOOLDIR:="$SCRIPT_DIR/isabelle/bin"}
  : ${ISABELLE:="$ISABELLE_TOOLDIR/isabelle"}
  : ${ISABELLE_BUILD:="$ISABELLE build -v"}

  [ -d "$AC_DIR"  ] || {
    echo >&2 "Cannot find \$AC_DIR ($AC_DIR)"
	  exit 1
  }

  # Location of Cogent compiler (if not already defined)
  : ${COGENT_TOOLDIR:="$SCRIPT_DIR/cogent/dist/build/cogent"}
  if ! type cogent >/dev/null 2>&1
  then PATH="$COGENT_TOOLDIR:$PATH"
  fi

  # Location of Cogent shared library
  : ${COGENT_STD_GUM_DIR:="$SCRIPT_DIR/cogent/lib"}
}

set_build_env
