#!/usr/bin/env bash

# Supporting Artifact for
# "Predictive Verification using Intrinsic Definitions of Data Structures"
# by Adithya Murali, Cody Rivera, and P. Madhusudan.
# 
# Artifact by Cody Rivera, 2023. 
#
# Supporting scripts for running Boogie benchmarks.

BOOGIE_3="boogie"
BOOGIE_OPTS=""
PYTHON_3="python3"
TIMEOUT=3600
TIME_FORMAT="\t%E real,\t%U user,\t%S sys"

SINGLE_LINKED_LIST_BENCH="
    impact-sets
    append 
    copy-all 
    delete-all 
    find 
    insert-back 
    insert-front"

SORTED_LIST_BENCH="
    impact-sets
    append 
    copy-all 
    delete-all 
    find 
    insert-back 
    insert-front"

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
SKIP_LIST="
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

bench_boogie() {
    STRUCTURE=$1
    METHODS=${!2}

    echo ""
    echo "Benchmarking data structure $STRUCTURE:"
    echo "============================================================"

    for method in $METHODS; do
        if [ -f boogie/$STRUCTURE/$method.bpl ]; then
            echo "$method not implemented"
            continue
        fi
        if list_contains "$SKIP_LIST" "$STRUCTURE::$method"; then
            echo "$method skipped intentionally"
            continue
        fi
        echo "verification not implemented"
    done
}

bench_boogie "single-linked-list" SINGLE_LINKED_LIST_BENCH
bench_boogie "sorted-list" SORTED_LIST_BENCH
bench_boogie "sorted-list-minmax" SORTED_LIST_MINMAX_BENCH
bench_boogie "circular-list" CIRCULAR_LIST_BENCH
bench_boogie "binary-search-tree" BINARY_SEARCH_TREE_BENCH
bench_boogie "treap" TREAP_BENCH
bench_boogie "avl-tree" AVL_TREE_BENCH
bench_boogie "red-black-tree" RED_BLACK_TREE_BENCH
bench_boogie "bst-scaffolding" BST_SCAFFOLDING_BENCH
bench_boogie "scheduler-queue" SCHEDULER_QUEUE_BENCH
