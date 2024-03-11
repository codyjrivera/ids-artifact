#!/usr/bin/env bash

# Supporting Artifact for
# "Predictable Verification using Intrinsic Definitions"
# by Anonymous Authors.
# 
# Artifact by Anonymous Author, 2023. 
#
# Supporting scripts for running Dafny benchmarks.

source ./dep-locations.sh

VER_TIMEOUT=36000
DAFNY_OPTS="--verification-time-limit $VER_TIMEOUT"
TIME_FORMAT="\t%e" # user+sys is not accurate with Dafny, so wall clock must be used.

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
    red-black-tree::insert
    scheduler-queue::bst-remove-root
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

dafny_method() {
    STRUCTURE=$1
    METHOD=$2
    RUN_ANYWAY=$3

    if ! [ -f "dafny/$STRUCTURE/$STRUCTURE.dfy" ]; then
        echo "data structure $STRUCTURE not implemented"
        return 1
    fi
    if ! [ -f "dafny/$STRUCTURE/$METHOD.dfy" ]; then
        echo "method $STRUCTURE::$METHOD not implemented"
        return 1
    fi
    if list_contains "$BLACKLIST" "$STRUCTURE::$METHOD" && (! $RUN_ANYWAY); then
        echo "method $STRUCTURE::$METHOD not run"
        return 1
    fi

    # Verify
    command time -o tmp_ver_time -f "$TIME_FORMAT" $DAFNY_4 verify $DAFNY_OPTS \
        "dafny/$STRUCTURE/$METHOD.dfy" 2>&1 >tmp_log
    if [ "$?" -gt 0 ]; then
        echo "method $STRUCTURE::$METHOD does not verify"
        cat tmp_log
        return 1
    fi

    totaltime=$(cat tmp_ver_time | awk '{s+=$1} END {printf "%.2f", s}')

    printf "%02dh%02dm%05.2fs    " $(echo -e "$totaltime/3600\n$totaltime%3600/60\n$totaltime%60"| bc)
    printf "($STRUCTURE::$METHOD)\n"

    rm -f tmp_*

    return 0
}

dafny_ds() {
    STRUCTURE=$1
    METHODS=${!2}

    echo ""
    echo "Benchmarking data structure $STRUCTURE with Dafny:"
    echo "============================================================"

    for method in $METHODS; do
        dafny_method $STRUCTURE $method false
    done

    return 0
}
