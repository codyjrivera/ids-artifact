#!/usr/bin/env bash

# Supporting Artifact for
# "Predictable Verification using Intrinsic Definitions"
# by Adithya Murali, Cody Rivera, and P. Madhusudan.
# 
# Artifact by Cody Rivera, 2024. 
#
# Snippet for running one Dafny benchmark.

source ./dafny-benchmarks.sh

if [ "$#" -ne 2 ]; then
    echo "Usage: $0 DATASTRUCTURE METHOD"
    exit 1
fi

STRUCTURE=$1
METHOD=$2
echo "Verifying $STRUCTURE::$METHOD with Dafny:"
echo ""

VERBOSE=true
dafny_method $STRUCTURE $METHOD true
exit $?
