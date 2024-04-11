#!/usr/bin/env bash

# Supporting Artifact for
# "Predictable Verification using Intrinsic Definitions"
# by Adithya Murali, Cody Rivera, and P. Madhusudan.
# 
# Artifact by Cody Rivera, 2023. 
#
# Supporting scripts for running Boogie benchmarks.
# (using a transplant script for implementing parametrized
# map updates).

source ../dep-locations.sh

BOOGIE_OPTS="/proverOpt:O:smt.mbqi=false /proverOpt:O:model.compact=false\
 /proverOpt:O:model.v2=true /proverOpt:O:pp.bv_literals=false\
 /proverOpt:O:smt.case_split=3 /proverOpt:O:auto_config=false\
 /proverOpt:O:type_check=true /proverOpt:O:smt.qi.eager_threshold=100\
 /proverOpt:O:smt.delay_units=true /proverOpt:O:smt.arith.solver=2\
 /proverOpt:O:smt.arith.nl=false"
PROVER="z3"
TIME_FORMAT="\t%e"
MAX_SPLITS=8

VERBOSE=false

SINGLE_LINKED_LIST_BENCH="
    impact-sets
    append 
    copy-all 
    delete-all 
    find
    insert-back 
    insert-front
    insert
    reverse"

SORTED_LIST_BENCH="
    impact-sets
    delete-all
    find
    insert
    merge
    reverse"

SORTED_LIST_MINMAX_BENCH="
    impact-sets
    concatenate
    find-last"

CIRCULAR_LIST_BENCH="
    impact-sets
    insert-front
    insert-back
    delete-front
    delete-back"

BINARY_SEARCH_TREE_BENCH="
    impact-sets
    find
    insert
    delete
    remove-root"

TREAP_BENCH="
    impact-sets
    find
    insert
    delete
    remove-root"

AVL_TREE_BENCH="
    impact-sets
    insert
    delete
    find-min
    balance"

RED_BLACK_TREE_BENCH="
    impact-sets
    insert
    delete
    find-min
    delete-left-fixup
    delete-right-fixup"

BST_SCAFFOLDING_BENCH="
    impact-sets
    delete-inside
    remove-root
    fix-depth"

SCHEDULER_QUEUE_BENCH="
    impact-sets
    move-request
    list-remove-first
    bst-delete-inside
    bst-remove-root
    bst-fix-depth"

# to contain items of form datastructure::method
BLACKLIST="
    "

list_contains() {
    LIST=$1
    VALUE=$2
    for x in $LIST; do
        if [ "$x" = "$VALUE" ]; then
            return 0
        fi
    done
    return 1
}

boogie_method() {
    STRUCTURE=$1
    METHOD=$2
    RUN_ANYWAY=$3

    if ! [ -f "$STRUCTURE/$STRUCTURE.bpl" ]; then
        echo "data structure $STRUCTURE not implemented"
        return 1
    fi
    if ! [ -f "$STRUCTURE/$METHOD.bpl" ]; then
        echo "method $STRUCTURE::$METHOD not implemented"
        return 1
    fi
    if list_contains "$BLACKLIST" "$STRUCTURE::$METHOD" && (! $RUN_ANYWAY); then
        echo "method $STRUCTURE::$METHOD not run"
        return 1
    fi

    # Get max number of splits in the program, if this exists.
    if max_splits=$(grep "SETUP:max-splits" "$STRUCTURE/$METHOD.bpl");
    then
        max_splits=$(echo $max_splits | awk -F '=|;' '{print $2}')
    else
        max_splits=$MAX_SPLITS
    fi

    # Resolve
    cat "$STRUCTURE/$STRUCTURE.bpl" "$STRUCTURE/$METHOD.bpl" >tmp_input.bpl
    command time -o tmp_boogie_time -f "$TIME_FORMAT" $BOOGIE_3 \
        /proverOpt:SOLVER=noop $BOOGIE_OPTS /vcsMaxSplits:$max_splits /proverLog:tmp_input.smt2 tmp_input.bpl \
        2>&1 >tmp_log
    if ! [ -f "tmp_input.smt2" ]; then
        echo "method $STRUCTURE::$METHOD does not resolve"
        cat tmp_log
        return 1
    fi

    # Transplant
    if [ -f "$STRUCTURE/$STRUCTURE.tp" ]; then
        command time -o tmp_transplant_time -f "$TIME_FORMAT" $PYTHON_3 \
            transplant.py tmp_input.smt2 "$STRUCTURE/$STRUCTURE.tp" 2>tmp_log >tmp_transplant.smt2
        
        if ! command time -o tmp_transplant_time -f "$TIME_FORMAT" $PYTHON_3 \
                transplant.py tmp_input.smt2 "$STRUCTURE/$STRUCTURE.tp" \
                2>tmp_log >tmp_transplant.smt2; then
            echo "method $STRUCTURE::$METHOD does not transplant"
            cat tmp_log
            return 1
        fi
    else
        cp tmp_input.smt2 tmp_transplant.smt2
    fi

    # Check for quantified reasoning
    if grep -q -e forall -e exists -e lambda tmp_transplant.smt2; then
        echo "method $STRUCTURE::$METHOD contains quantified reasoning in its SMT script"
        return 1
    fi

    # VERBOSE: Print number of asserts
    if $VERBOSE; then
        printf "There are "
        printf "%d" `grep -o "(check-sat)" tmp_transplant.smt2 | wc -l`
        printf " verification conditions in $STRUCTURE::$METHOD\n"
    fi

    # Prove
    command time -o tmp_prover_time -f "$TIME_FORMAT" $PROVER \
        tmp_transplant.smt2 2>&1 >tmp_log
    if grep -q ^sat$ tmp_log || grep -q ^unknown$ tmp_log; then
        echo "method $STRUCTURE::$METHOD does not verify"
        cat tmp_log
        return 1
    fi

    totaltime=$(cat tmp_boogie_time tmp_transplant_time tmp_prover_time | awk '{s+=$1} END {printf "%.2f", s}')

    printf "%02dh%02dm%05.2fs    " $(echo -e "$totaltime/3600\n$totaltime%3600/60\n$totaltime%60"| bc)
    printf "($STRUCTURE::$METHOD)\n"

    rm -f tmp_*

    return 0
}

boogie_ds() {
    STRUCTURE=$1
    METHODS=${!2}

    echo ""
    echo "Benchmarking data structure $STRUCTURE with Boogie:"
    echo "============================================================"

    for method in $METHODS; do
        boogie_method $STRUCTURE $method false
    done

    return 0
}
