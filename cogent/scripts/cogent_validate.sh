#!/bin/bash

#
# Copyright 2018, Data61
# Commonwealth Scientific and Industrial Research Organisation (CSIRO)
# ABN 41 687 119 230.
#
# This software may be distributed and modified according to the terms of
# the GNU General Public License version 2. Note that NO WARRANTY is provided.
# See "LICENSE_GPLv2.txt" for details.
#
# @TAG(DATA61_GPL)
#

cd "$(dirname "${BASH_SOURCE[0]}")"

#Directories
COGENTDIR=../
TLD=../../

source $TLD/build-env.sh || exit

# Check for getopt
getopt -T >/dev/null
if [[ $? != 4 ]]
then
  echo "$0: error: GNU getopt not available"
  exit 1
fi

# Usage
long_usage()
{
    echo "Usage: $0 -[pp|tc|ds|an|mn|cg|gcc|tc-proof|ac|flags|hsc-gen|aq|shallow-proof|hs-shallow|examples|goanna|libgum|all|clean] [-q|-i|]"
    echo 'Run (one or more) tests for the Cogent compilation tools.'
    echo '  -pp      Test the parser and the pretty-printer are roughly inverse of each other'
    echo '  -tc      Test type checking'
    echo '  -ds      Test desugaring'
    echo '  -an      Test A-normal transform'
    echo '  -mn      Test monomorphization'
    echo '  -cg      Test code generation'
    echo '  -gcc     Compile generated code using GCC'
    echo '  -tc-proof  Test proof generation for type checking'
    echo '  -ac      Read generated code using Isabelle'
    echo '  -flags   Test compiler features enabled by flags'
    echo '  -aq      Test antiquotation'
    echo '  -shallow-proof Test shallow-emdedding proofs'
    echo '  -hs-shallow    Test Haskell shallow embedding generation and compiler with GHC'
    echo '  -examples      Build all examples'
    echo '  -goanna  Check generated code using Goanna (dependency: Goanna)'
    echo '  -ee      Test end-to-end proof'
    echo '  -libgum  Test shared library'
    echo
    echo '  -all     Run all tests'
    echo '  -clean   Delete generated files'
    echo '  -q       Do not print output for failed tests'
    echo '  -i       Prompt before major removals'
}

short_usage()
{
    echo "Usage: $0 -[pp|tc|ds|an|mn|cg|gcc|tc-proof|ac|flags|hsc-gen|aq|shallow-proof|hs-shallow|examples|goanna|libgum|all|clean] [-q|-i|]"
    echo 'Run with -h for detailed explanation of all the options.'
}

# Parse options
OPTS=$(getopt -o h --alternative --long pp,tc,ds,an,mn,cg,gcc,tc-proof,ac,flags,hsc-gen,aq,shallow-proof,hs-shallow,examples,goanna,ee,libgum,all,help,clean,q,i -n "$0" -- "$@")
if [ $? != 0 ]
then
    short_usage
    exit 1
fi

eval set -- "$OPTS"

# Parse Arguments
TESTSPEC=''
DO_CLEAN=0
QUIET=0
INTERACTIVE=0

while true; do
    case "$1" in
        -h|--help)
            long_usage
            exit;;
        --) shift; break;;
        --q) QUIET=1; shift;;
        --i) INTERACTIVE=1; shift;;
        --clean) DO_CLEAN=1; shift;;
        --all) TESTSPEC='--pp--tc--ds--an--mn--aq--cg--gcc--tc-proof--hsc-gen--ac--flags--shallow-proof--hs-shallow--goanna--ee--libgum'; shift;;
        *) TESTSPEC="${TESTSPEC}$1"; shift;;
    esac
done

if [[ $DO_CLEAN = 1 && "$TESTSPEC" != '' ]]
  then echo "$0: cannot run --clean and tests at the same time" >&2
       exit 1
fi
# Just compile the compiler if no option is given
if [[ $DO_CLEAN = 0 && "$TESTSPEC" = '' ]]
then
    short_usage
    exit 1
fi
TESTSPEC="${TESTSPEC}--"
# Now $TESTSPEC contains test options separated by --

if [ "$#" -ne 0 ]
then echo "$0: error: extra argument '$1'" >&2
     exit 1
fi

if [[ -t 1 ]]
then
  txtbld=$(tput bold)             # Bold
  bldred=${txtbld}$(tput setaf 1) # Red
  bldgrn=${txtbld}$(tput setaf 2) # Green
  txtrst=$(tput sgr0)             # Reset
else
  txtbld=
  bldred=
  bldgrn=
  txtrst=
fi

TESTS=$COGENTDIR/tests
COUT=$COGENTDIR/out
ABS=$COGENTDIR/out/abstract
: ${CC:=cc}

if [ -z "$CGFLAGS" ]; then CGFLAGS="--fno-static-inline"; fi

TCFLAGS="$VFLAGS $TCFLAGS"
DSFLAGS="$VFLAGS $DSFLAGS"
ANFLAGS="$VFLAGS $ANFLAGS"
MNFLAGS="$VFLAGS $MNFLAGS"
CGFLAGS="$VFLAGS $CGFLAGS"

ISABELLE_SESSION_NAME=CogentTestTemporary
ISABELLE_TIMEOUT=300

if [[ $DO_CLEAN = 1 ]]
  then echo "rm -r $COUT"
       rm -r "$COUT"
       exit
fi

# Resolve dependencies
HAVE_DONE_CG=1
HAVE_DONE_GCC=1
if [ ! -d "$COUT" ]
  then HAVE_DONE_CG=0
fi
if [ ! -d "$ABS" ]
  then HAVE_DONE_GCC=0
fi

# FIXME: refactor
if [[ "$TESTSPEC" =~ '--ac--' && ! ( "$TESTSPEC" =~ '--gcc--' ) && $HAVE_DONE_GCC = 0 ]]
  then echo 'Note: adding --gcc because --ac depends on it' >&2
       TESTSPEC="${TESTSPEC}gcc--"
fi
if [[ "$TESTSPEC" =~ '--hsc-gen--' && ! ( "$TESTSPEC" =~ '--gcc--' ) && $HAVE_DONE_GCC = 0 ]]
  then echo 'Note: adding --gcc because --hsc-gen depends on it' >&2
  # -gcc helps to tweak the .h files to include the right things
       TESTSPEC="${TESTSPEC}gcc--"
fi
if [[ "$TESTSPEC" =~ '--goanna--' && ! ( "$TESTSPEC" =~ '--gcc--' ) && $HAVE_DONE_GCC = 0 ]]
  then echo 'Note: adding --gcc because --goanna depends on it' >&2
       TESTSPEC="${TESTSPEC}gcc--"
fi
if [[ "$TESTSPEC" =~ '--ac--' && ! ( "$TESTSPEC" =~ '--cg--' ) && $HAVE_DONE_CG = 0 ]]
  then echo 'Note: adding --cg because --ac depends on it' >&2
       TESTSPEC="${TESTSPEC}cg--"
fi

if [[ "$TESTSPEC" =~ '--goanna--' && ! ( "$TESTSPEC" =~ '--cg--' ) && $HAVE_DONE_CG = 0 ]]
  then echo 'Note: adding --cg because --goanna depends on it' >&2
       TESTSPEC="${TESTSPEC}cg--"
fi
# This must come after all tests that -gcc needs be added.
if [[ "$TESTSPEC" =~ '--gcc--' && ! ( "$TESTSPEC" =~ '--cg--' ) && $HAVE_DONE_CG = 0 ]]
  then echo 'Note: adding --cg because --gcc depends on it' >&2
       TESTSPEC="${TESTSPEC}cg--"
fi

echo "TESTSPEC = $TESTSPEC"

# check_output [>file] cmd...
# Equivalent to running "cmd... [>file]" except the output is
# suppressed if cmd returns 0.
check_output() {
  local text ret
  if [[ "$1" =~ ^\> ]]
  then REDIR="${1:1}"
       shift
       text=$("$@" 2>&1 >"$REDIR")
  else text=$("$@" 2>&1)
  fi
  ret=$?
  if [[ $ret != 0 && $QUIET = 0 ]]
  then echo "$text"
  fi
  return $ret
}

gen_test_hdrs() {
    mkdir -p $COGENTDIR/tests/include
    pushd tests 2>&1 > /dev/null

    for fname in *.cogent;
    do
        dfname="${fname%.*}_dummy.h"
        #echo "Generating include/$dfname from $fname"
        egrep "^type +([A-Z][a-zA-Z0-9_']*)( [a-z][a-zA-Z0-9_']*)* *(--.*)?$" $fname | sed -e "s/type \([A-Z][a-zA-Z0-9_']*\).*$/typedef void* \1;/" > include/$dfname
    done

    popd 2>&1 > /dev/null
}

pass_msg="${bldgrn}pass${txtrst}"
goodfail_msg="${bldgrn}fail (as expected)${txtrst}"
fail_msg="${bldred}FAIL${txtrst}"
badpass_msg="${bldred}passed but should FAIL${txtrst}"


if [[ -z "$COGENT" ]]; then COGENT=cogent; fi
if [[ -z "$GHC" ]]; then GHC=ghc; fi
if [[ -z "$HSC2HS" ]]; then HSC2HS=hsc2hs; fi
if [[ -z "$HC_PKG" ]]; then HC_PKG=ghc-pkg; fi
if [[ -z "$DIST" ]]; then DIST=dist; fi
if [[ -z "$PACKAGE_DB" ]]; then
  PACKAGE_DB="${CABAL_SANDBOX}/`arch`-`uname | tr [A-Z] [a-z]`-ghc-`${GHC} --version | sed -e 's/^.*version //'`-packages.conf.d"
fi

# Generate the test headers
#gen_test_hdrs

declare -i all_passed=0 all_total=0 all_ignored=0
declare -i passed total

test_parser_prettyprinter()
{
    echo "=== Parser ==="
    all_total+=1
    passed=0
    total=0

    if [ -e "$COUT" -a -d "$COUT" ]
    then echo "rm -r $COUT"
         rm -r "$COUT"
    fi
    mkdir -p "$COUT" || exit
    for source in "$TESTS"/pass_*.cogent
    do
        echo -n "$source: "
        f=$(basename "$source")
        total+=1
        if check_output ">$COUT/$f" $COGENT --pretty-parse "$source" && \
           check_output $COGENT --parse "$COUT/$f"
        then passed+=1; echo "$pass_msg"
        else echo "$fail_msg"
        fi
    done

    # rm -rf "$COUT"
    echo "Passed $passed out of $total."
    if [[ $passed = $total ]]
    then all_passed+=1
    fi

}

test_type_checking()
{
    echo "=== Type checking ($TCFLAGS) ==="
    all_total+=1
    passed=0
    total=0

    for source in "$TESTS"/pass_*.cogent
    do
        echo -n "  $(basename $source): "
        total+=1
        if check_output $COGENT -t "$source" $TCFLAGS
        then passed+=1; echo "$pass_msg"
        else echo "$fail_msg"
        fi
    done

    for source in "$TESTS"/fail_*.cogent
    do
        echo -n "  $(basename $source): "
        total+=1
        $COGENT -t "$source" $TCFLAGS 2>/dev/null # avoid check_output
        ret=$?
        if [ $ret -eq 134 ]
        then passed+=1; echo "$goodfail_msg"
        elif [ $ret -eq 0 ]
        then echo "$badpass_msg"
        else echo "${bldred}Compiler crashed!!${txtrst}"
        fi
    done

    declare -i should shouldpass shouldfail wip
    should=0
    shouldpass=0
    shouldfail=0

    for source in "$TESTS"/shouldpass_*.cogent
    do
        should+=1
        shouldpass+=1
    done

    for source in "$TESTS"/shouldfail_*.cogent
    do
        should+=1
        shouldfail+=1
    done

    wip=0

    for source in "$TESTS"/wip_*.cogent
    do
        wip+=1
    done

    echo "Passed $passed out of $total."
    if [[ $passed = $total ]]
    then all_passed+=1
    fi
    echo "$should problems we are aware of:"
    echo "* $shouldpass should pass but don't:"
    find "$TESTS" -name "shouldpass_*.cogent" -printf "  %f\n"
    echo "* $shouldfail should fail but don't:"
    find "$TESTS" -name "shouldfail_*.cogent" -printf "  %f\n"
    echo "* $wip are still under development and don't work ATM"
    find "$TESTS" -name "wip_*.cogent" -printf "  %f\n"
}

test_desugaring()
{
    echo "=== Desugaring ($DSFLAGS) ==="
    all_total+=1
    passed=0
    total=0

    for source in "$TESTS"/pass_*.cogent
    do
        echo -n "$source: "
        total+=1
        if check_output $COGENT --desugar "$source" -w $DSFLAGS
        then passed+=1; echo "$pass_msg"
        else echo "$fail_msg"
        fi
    done

    echo "Passed $passed out of $total."
    if [[ $passed = $total ]]
    then all_passed+=1
    fi
}

test_anf()
{
    echo "=== A-normal transform ($ANFLAGS) ==="
    all_total+=1
    passed=0
    total=0

    for source in "$TESTS"/pass_*.cogent
    do
        echo -n "$source: "
        total+=1
        if check_output $COGENT --normal "$source" -w $ANFLAGS
        then passed+=1; echo "$pass_msg"
        else echo "$fail_msg"
        fi
    done

    echo "Passed $passed out of $total."
    if [[ $passed = $total ]]
    then all_passed+=1
    fi
}

test_monomorphization()
{
    echo "=== Monomorphization ($MNFLAGS) ==="
    all_total+=1
    passed=0
    total=0

    for source in "$TESTS"/pass_*.cogent
    do
        echo -n "$source: "
        total+=1
        if check_output $COGENT --mono "$source" -w $MNFLAGS
        then passed+=1; echo "$pass_msg"
        else echo "$fail_msg"
        fi
    done

    echo "Passed $passed out of $total."
    if [[ $passed = $total ]]
    then all_passed+=1
    fi
}

test_code_generation()
{
    echo "=== Code generation ($CGFLAGS) ==="
    all_total+=1
    passed=0
    total=0

    if [ -e "$COUT" -a -d "$COUT" ]
    then echo "rm -r $COUT"
         rm -r "$COUT"
    fi
    mkdir -p "$COUT" || exit  # code-gen will keep `out' directory
    for source in "$TESTS"/pass_*.cogent
    do
        echo -n "$source: "
        total+=1
        if check_output $COGENT -g "$source" --dist-dir="$COUT" -w $CGFLAGS
        then passed+=1; echo "$pass_msg"
        else echo "$fail_msg"
        fi
    done

    echo "Passed $passed out of $total."
    if [[ $passed = $total ]]
    then all_passed+=1
    fi
}

test_gcc()
{
    echo '=== GCC test ==='
    all_total+=1
    passed=0
    total=0

    for hfile in "$COUT"/pass_*.h
    do
        outfile=`basename "$hfile" .h`
        abs="$ABS/$outfile/abstract"
        if [ -e "$abs/$outfile" -a -d "$abs" ]
        then echo "rm -r $abs"
             rm -r "$abs"
        fi
        mkdir -p "$abs" || exit
        echo -n "${outfile}.cogent: "
        total+=1
        sed -i -r 's/^#include <cogent-defns.h>/#include \"..\/lib\/cogent-defns.h\"/' "$hfile"
        sed -i -r "s|^#include <abstract/([^\.]*).h>|#include \"$abs/\1.h\"|g" "$hfile"
        for abstract_h in `egrep "^#include \"$abs\/([^\.]*).h\"" "$hfile" | \
                       sed -r "s|#include \"$abs/([^\.]*).h\"|\1|"`; do
            echo "typedef void* $abstract_h;" > "$abs/${abstract_h}.h"
        done
        if ! fgrep -q "#include \"../tests/include/${outfile}_dummy.h\"" "$hfile"
        then (echo "#include \"../tests/include/${outfile}_dummy.h\"" && cat "$hfile") > "$hfile.tmp"
             mv "$hfile.tmp" "$hfile"
        fi

        if check_output "$CC" -c "$COUT/${outfile}.c" -o "$COUT/${outfile}.o" -Wall -Werror -Wno-unused -pedantic -std=c99 -I"$TESTS"
        then passed+=1; echo "$pass_msg"
        else echo "$fail_msg"
        fi
    done

    echo "Passed $passed out of $total."
    if [[ $passed = $total ]]
    then all_passed+=1
    fi
}

test_isabelle_type_proof()
{
    echo '=== Isabelle (type proof) test ==='
    all_total+=1
    passed=0
    total=0

    mkdir -p "$COUT" || exit
    if ! type $ISABELLE >/dev/null 2>&1 # Sanity check
    then echo "${bldred}Error:${txtrst} could not find Isabelle program (check \"$ISABELLE_TOOLDIR\")."
    else
        COGENTHEAPNAME="CogentTyping"
        echo -n '* Preparing Cogent theory heap... '
        COGENTHEAPSPEC="session \"$COGENTHEAPNAME\" = \"HOL-Word\" + \
options [timeout=$ISABELLE_TIMEOUT] theories [quick_and_dirty] \
\"../isa/CogentHelper\""
        echo "$COGENTHEAPSPEC" > "$COUT/ROOT"
        if ! check_output $ISABELLE build -d "$COUT" -b "$COGENTHEAPNAME"
        then
            echo "${bldred}failed to build Cogent theory!${txtrst}"
        else
            echo "built session $COGENTHEAPNAME"
            for source in "$TESTS"/pass_*.cogent
            do THYNAME_TEMP=$(basename "$source" .cogent | tr - _)_TypeProof
               THYNAME="${THYNAME_TEMP^}" # make valid theory name, need be careful
               THY="$COUT/$THYNAME.thy"
               echo -n "$(basename "$source"): "
               total+=1
               echo "$COGENTHEAPSPEC" > "$COUT/ROOT"
               echo "session \"$ISABELLE_SESSION_NAME\" = \"$COGENTHEAPNAME\" + options [timeout=$ISABELLE_TIMEOUT] theories [quick_and_dirty] \"$THYNAME\"" >> "$COUT/ROOT"

               if check_output $COGENT --type-proof --fml-typing-tree "$source" --root-dir="../../"  --dist-dir="$COUT"
               then
                   sed -i -e 's,"ProofTrace","../isa/ProofTrace",' "$COUT/$THYNAME.thy"
                   if check_output $ISABELLE build -d "$COUT" "$ISABELLE_SESSION_NAME"
                   then passed+=1; echo "$pass_msg"
                   else echo "$fail_msg"
                   fi
               else
                   echo "$source: ${bldred}Compiler failed!!${txtrst}"
               fi
            done

            echo "Passed $passed out of $total."
            if [[ $passed = $total ]]
            then all_passed+=1
            fi
        fi
    fi
}

test_autocorres()
{
    echo '=== Isabelle (AutoCorres) test ==='
    all_total+=1
    passed=0
    total=0

    if ! type $ISABELLE >/dev/null 2>&1 # Sanity check
    then echo "${bldred}Error:${txtrst} could not find Isabelle program (check \"$ISABELLE_TOOLDIR\")."
    else
        for source in "$TESTS"/pass_*.cogent
        do echo "${source}: "
           cfile=$(basename $source .cogent).c
           total+=1
           $COGENT --c-refinement --proof-input-c="$cfile" --root \
                   --dist-dir="$COUT" --root-dir=../../ --proof-name="$ISABELLE_SESSION_NAME" "$source"
           sed -i -e "s/^session ${ISABELLE_SESSION_NAME}_ACInstall = ${ISABELLE_SESSION_NAME}_SCorres_Normal +$/session ${ISABELLE_SESSION_NAME}_ACInstall = AutoCorres +/" "$COUT/ROOT"

           if check_output $ISABELLE_BUILD -d "$L4V_DIR" -d "../isa" -d "$COUT" ${ISABELLE_SESSION_NAME}_ACInstall
           then passed+=1; echo "$pass_msg"
           else echo "$fail_msg"
           fi
        done

        echo "Passed $passed out of $total."
        if [[ $passed = $total ]]
        then all_passed+=1
        fi
    fi
}

test_end_to_end()
{
    echo '=== End-to-end test ==='
    all_total+=1
    passed=0
    total=0

    if ! type $ISABELLE >/dev/null 2>&1 # Sanity check
    then echo "${bldred}Error:${txtrst} could not find Isabelle program (check \"$ISABELLE_TOOLDIR\")."
    else
        rm -r "$COUT"
        mkdir -p "$COUT"
        for source in "$TESTS"/pass_*.cogent
        do echo -n ""$source": "
           outfile=$(basename "$source" .cogent)
           hfile="$COUT/${outfile}.h"
           total+=1
           abs="$ABS/$outfile/abstract"
           if [ -e "$abs/$outfile" -a -d "$abs" ]
           then echo "rm -r $abs"
                rm -r "$abs"
           fi
           mkdir -p "$abs" || exit
           echo -n "${outfile}.cogent: "
           $COGENT -A --fml-typing-tree --root-dir=../../ --dist-dir="$COUT" "$source" --proof-name="$ISABELLE_SESSION_NAME"
           sed -i -r 's|^#include <cogent-defns.h>|#include \"../test/cogent.h\"|' "$hfile"
           sed -i -r "s|^#include <abstract/([^\.]*).h>|#include \"$abs/\1.h\"|g" "$hfile"
           for abstract_h in `egrep "^#include \"$abs\/([^\.]*).h\"" "$hfile" | \
                          sed -r "s|#include \"$abs/([^\.]*).h\"|\1|"`; do
               echo "typedef void* $abstract_h;" > "$abs/${abstract_h}.h"
           done
           if ! fgrep -q "#include \"../tests/include/${outfile}_dummy.h\"" "$hfile"
           then (echo "#include \"../tests/include/${outfile}_dummy.h\"" && cat "$hfile") > "$hfile.tmp"
                mv "$hfile.tmp" "$hfile"
           fi

           if check_output $ISABELLE_BUILD -d "$L4V_DIR" -d "$COUT" -d "../isa" ${ISABELLE_SESSION_NAME}_AllRefine
           then passed+=1; echo "$pass_msg"
           else echo "$fail_msg"
           fi
        done

        echo "Passed $passed out of $total."
        if [[ $passed = $total ]]
        then all_passed+=1
        fi
    fi
}

test_cogent_flags()
{
    echo '=== Test different Cogent flags ==='
    all_total+=1
    passed=0
    total=0

    for dir in "$TESTS"/pass_flags_*
    do
        echo -n "$dir: "
        total+=1
        if (cd "$dir" && check_output sh BUILD)
        then passed+=1; echo "$pass_msg"
        else echo "$fail_msg"
        fi
    done

    for dir in "$TESTS"/fail_flags_*
    do
        echo -n "$dir: "
        total+=1
        (cd "$dir" && sh BUILD 2> /dev/null)
        ret=$?
        if [ $ret -eq 0 ]
        then echo "$badpass_msg"
        elif [ $ret -eq 134 ]
        then passed+=1; echo "$goodfail_msg"
        else  # unexpected failures
            echo "$fail_msg"
        fi
    done

    echo "Passed $passed out of $total."
    if [[ $passed -eq $total ]]
    then all_passed+=1
    fi
}

test_antiquotation()
{
    echo '=== Antiquotation ==='
    all_total+=1
    passed=0
    total=0

    for dir in "$TESTS"/antiquote-tests/pass_*
    do
        echo -n "$dir: "
        total+=1
        if (cd "$dir" && check_output sh BUILD)
        then passed+=1; echo "$pass_msg"
        else echo "$fail_msg"
        fi
    done

    echo "Passed $passed out of $total."
    if [[ $passed = $total ]]
    then all_passed+=1
    fi
}

test_shallow_embedding()
{
    echo '=== Shallow-embedding ==='
    all_total+=1
    passed=0
    total=2

    for i in tests
    do
        if (cd ../isa/shallow/tests && check_output make $i)
        then
            passed+=1;
            echo "$pass_msg" ;
        else
            echo "$fail_msg"
        fi
    done

    if [[ $passed -eq 1 ]]
    then
        for i in ShallowT
        do
            if (cd ../isa/shallow/ && check_output $ISABELLE build -d ../ -b $i)
            then
                passed+=1;
                echo "$pass_msg" ;
            else
  	        echo "$fail_msg"
            fi
        done
    fi

    # undo all uncomited changes by make [tests|ext2]
    (cd ../isa/shallow/ && git checkout .)

    echo "Passed $passed out of $total."
    if [[ $passed = $total ]]
    then all_passed+=1
    fi
}

test_haskell_shallow_embedding()
{
    echo "=== Haskell shallow embedding ==="
    all_total+=1
    passed=0
    total=0

    if [[ ! -e "$COUT" ]]; then
        mkdir "$COUT"
    fi

    for source in "$TESTS"/pass_*.cogent
    do
        echo $source
        total+=1
        name=$(basename $source .cogent)
        name=`echo ${name^} | tr "-" "_"`
        if check_output cogent --hs-shallow-desugar --dist-dir="$COUT" --proof-name="$name" $source
        then $GHC -w "$COUT"/"$name"_Shallow_Desugar.hs -package-db="$PACKAGE_DB" && passed+=1 && echo "$pass_msg" ;
        else echo "$fail_msg"
        fi
    done

    echo "Passed $passed out of $total."
    if [[ $passed = $total ]]
    then all_passed+=1
    fi
}

test_hsc_gen()
{
    echo "=== Test .hsc file generation ==="
    all_total+=1
    passed=0
    total=0

    if [[ ! -e "$COUT" ]]; then
        mkdir "$COUT"
    fi

    for source in "$TESTS"/pass_*.cogent
    do
        echo $source
        total+=1
        name=$(basename $source .cogent)
        name=`echo ${name^} | tr "-" "_"`
        if check_output cogent --ffi-hsc --dist-dir="$COUT" --proof-name="$name" $source
        then $HSC2HS -I "$COUT" -I "$COGENTDIR"/lib -I "$TESTS" "$COUT"/"$name"_FFI.hsc && passed+=1 && echo "$pass_msg" ;
        else echo "$fail_msg"
        fi
    done

    echo "Passed $passed out of $total."
    if [[ $passed = $total ]]
    then all_passed+=1
    fi
}

test_examples()
{
    echo "=== Building examples ==="
    all_total+=1
    passed=0
    total=0

    pushd "$COGENTDIR"/examples

    for ex in */
    do
        pushd $ex
        echo $ex
        total+=1
        if check_output make
        then passed+=1; echo $pass_msg
        else echo $fail_msg
        fi
        popd
    done

    echo "Passed $passed out of $total."
    if [[ $passed = $total ]]
    then all_passed+=1
    fi
    popd
}

test_goanna()
{
    echo '=== Goanna test ==='
    echo 'Note: Goanna tests are currently not counted.' # FIXME?
    all_total+=1
    all_ignored+=1

    if ! type goannacc >/dev/null 2>&1 # Sanity check
    then echo "${bldred}Error:${txtrst} could not find goannacc."
    else
        for source in "$COUT"/*.c
        do
            echo -n "$source: "
            check_output goannacc --nc --all-checks --output-format="%LINENO%: %CHECKNAME%%EOL%" "$source"
        done
    fi
}

test_libgum()
{
    all_total+=1
    TEST_FILE=_regression.cogent
    pushd "$COGENTDIR"/lib

    # ensure set
    shopt -s globstar
    # since some libgum stuff depends on this type
    echo $'type FsInode\ntype FsState\ntype VfsSuperBlock\ncogent_LOG_LEVEL: U32\ncogent_LOG_LEVEL = 0' > "$TEST_FILE"

    flist=`find gum -name "*.cogent"`
    echo $flist
    # include everything
    for src in $flist
    do
        echo "include <$src>" >> "$TEST_FILE"
    done

    # typecheck, and save result
    cogent -t "$TEST_FILE"
    code=$?

    rm "$TEST_FILE"

    echo -n "libgum typechecking: "
    if [ $code -eq 0 ]; then
  	all_passed+=1
        echo "$pass_msg"
    else
        echo "$fail_msg"
    fi
}

#
# TODO: We will have to refactor th following 'if' statement blocks
#
if [[ "$TESTSPEC" =~ '--pp--' ]];
then
    test_parser_prettyprinter
fi
if [[ "$TESTSPEC" =~ '--tc--' ]];
then
    test_type_checking
fi

if [[ "$TESTSPEC" =~ '--ds--' ]];
then
    test_desugaring
fi

if [[ "$TESTSPEC" =~ '--an--' ]];
then
    test_anf
fi

if [[ "$TESTSPEC" =~ '--mn--' ]];
then
    test_monomorphization
fi

if [[ "$TESTSPEC" =~ '--cg--' ]];
then
    test_code_generation
fi

if [[ "$TESTSPEC" =~ '--gcc--' ]];
then
    test_gcc
fi

if [[ "$TESTSPEC" =~ '--tc-proof--' ]];
then
    test_isabelle_type_proof
fi


if [[ "$TESTSPEC" =~ '--ac--' ]];
then
    test_autocorres
fi


if [[ "$TESTSPEC" =~ '--ee--' ]];
then
    test_end_to_end
fi

if [[ "$TESTSPEC" =~ '--flags--' ]];
then
    test_cogent_flags
fi

if [[ "$TESTSPEC" =~ '--aq--' ]];
then
    test_antiquotation
fi

if [[ "$TESTSPEC" =~ '--shallow-proof--' ]];
then
    test_shallow_embedding
fi

if [[ "$TESTSPEC" =~ '--hs-shallow' ]];
then
    test_haskell_shallow_embedding
fi

if [[ "$TESTSPEC" =~ '--hsc-gen' ]];
then
    test_hsc_gen
fi

if [[ "$TESTSPEC" =~ '--examples' ]];
then
    test_examples
fi

if [[ "$TESTSPEC" =~ '--goanna--' ]];
then
    test_goanna
fi

if [[ "$TESTSPEC" =~ '--libgum--' ]];
then
    test_libgum
fi

SUMMARY="Test suites: $all_total; passed: $all_passed"
exit_code=0
if [[ $(($all_total - $all_ignored)) != $all_passed ]]
  then SUMMARY+="; failed: "$(($all_total - $all_ignored - $all_passed))
       exit_code=1
fi
if [[ $all_ignored != 0 ]]
  then SUMMARY+="; $all_ignored not counted"
fi

echo '=== SUMMARY ==='
echo "$SUMMARY"
exit $exit_code
