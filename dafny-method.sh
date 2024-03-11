#!/usr/bin/env bash

# Supporting Artifact for
# "Predictable Verification using Intrinsic Definitions"
# by Anonymous Authors.
# 
# Artifact by Anonymous Author, 2023. 
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
