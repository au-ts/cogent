#!/bin/bash

#
# Runs AllRefine on the generated bilbyfs proofs
#

if [[ ! -f "plat/verification/BilbyFs_AllRefine.thy" ]]
then
    echo "Error - Cannot find BilbyFs_AllRefine.thy"
    exit
fi

export L4V_ARCH="ARM";

# This gives java more heap space to use, so it won't crash as often
export ISABELLE_BUILD_JAVA_OPTIONS="-Xms2048m -Xmx12288m -Xss4m";

export REPO_ROOT="../../../.."

export ISABELLE_IDENTIFIER="BilbyFs2019Benchmark"

time isabelle build -d plat/verification \
                    -d $REPO_ROOT \
                    -d $REPO_ROOT/autocorres \
                    -b -o process_output_limit=999 \
                     BilbyFs_AllRefine;
