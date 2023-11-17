#!/usr/bin/env bash

# Supporting Artifact for
# "Predictable Verification using Intrinsic Definitions of Data Structures"
# by Anonymous Authors.
# 
# Artifact by Anonymous Author, 2023. 
#
# Snippet for running all Boogie benchmarks.

source ./boogie-benchmarks.sh

boogie_ds "single-linked-list" SINGLE_LINKED_LIST_BENCH
boogie_ds "sorted-list" SORTED_LIST_BENCH
boogie_ds "sorted-list-minmax" SORTED_LIST_MINMAX_BENCH
boogie_ds "circular-list" CIRCULAR_LIST_BENCH
boogie_ds "binary-search-tree" BINARY_SEARCH_TREE_BENCH
boogie_ds "treap" TREAP_BENCH
boogie_ds "avl-tree" AVL_TREE_BENCH
boogie_ds "red-black-tree" RED_BLACK_TREE_BENCH
boogie_ds "bst-scaffolding" BST_SCAFFOLDING_BENCH
boogie_ds "scheduler-queue" SCHEDULER_QUEUE_BENCH
