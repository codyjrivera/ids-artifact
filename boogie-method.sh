#!/usr/bin/env bash

# Supporting Artifact for
# "Predictable Verification using Intrinsic Definitions"
# by Anonymous Authors.
# 
# Artifact by Anonymous Author, 2023-2024. 
#
# Snippet for running one Boogie benchmark.

source ./boogie-benchmarks.sh

if [ "$#" -ne 2 ]; then
    echo "Usage: $0 DATASTRUCTURE METHOD"
    exit 1
fi

STRUCTURE=$1
METHOD=$2
echo "Verifying $STRUCTURE::$METHOD with Boogie:"
echo ""

VERBOSE=true
boogie_method $STRUCTURE $METHOD true
exit $?
