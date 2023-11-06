#!/usr/bin/env bash

# Supporting Artifact for
# "Predictive Verification using Intrinsic Definitions of Data Structures"
# by Adithya Murali, Cody Rivera, and P. Madhusudan.
# 
# Artifact by Cody Rivera, 2023. 
#
# Snippet for running one Boogie benchmark.

source ./boogie-benchmarks.sh

if [ "$#" -ne 2 ]; then
    echo "Usage: $0 DATASTRUCTURE METHOD"
fi

STRUCTURE=$1
METHOD=$2
echo "Verifying $STRUCTURE::$METHOD with Boogie:"
echo ""

boogie_method $STRUCTURE $METHOD true
exit $?
