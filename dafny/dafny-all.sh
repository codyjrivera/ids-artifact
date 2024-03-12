#!/usr/bin/env bash

# Supporting Artifact for
# "Predictable Verification using Intrinsic Definitions"
# by Anonymous Authors.
# 
# Artifact by Anonymous Author, 2024. 
#
# Snippet for running all Dafny benchmarks.

source ./dafny-benchmarks.sh

dafny_ds "single-linked-list" SINGLE_LINKED_LIST_BENCH
dafny_ds "sorted-list" SORTED_LIST_BENCH
dafny_ds "sorted-list-minmax" SORTED_LIST_MINMAX_BENCH
dafny_ds "circular-list" CIRCULAR_LIST_BENCH
dafny_ds "binary-search-tree" BINARY_SEARCH_TREE_BENCH
dafny_ds "treap" TREAP_BENCH
dafny_ds "avl-tree" AVL_TREE_BENCH
dafny_ds "red-black-tree" RED_BLACK_TREE_BENCH
dafny_ds "bst-scaffolding" BST_SCAFFOLDING_BENCH
dafny_ds "scheduler-queue" SCHEDULER_QUEUE_BENCH
