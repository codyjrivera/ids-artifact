// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions"
// by Anonymous Authors.
// 
// Artifact by Anonymous Author, 2023. 
//
// Impact set verification for Scheduler Queue.

include "scheduler-queue.dfy"

method Check_Create(k: int, arb1: QueueNode, arb2: QueueNode)
{
    assume arb1.BST_LC();
    assume arb2.List_LC();
    var node := new QueueNode(k);
    // Note that arb cannot be node anyway
    assert arb1.BST_LC();
    assert arb2.List_LC();
}

method Check_Set_k(x: QueueNode, k: int, arb1: QueueNode, arb2: QueueNode)
    modifies x
{
    assume arb1.BST_LC();
    assume arb2.List_LC();
    assume arb1 != x;
    assume arb2 != x;
    x.k := k;
    assert arb1.BST_LC();
    assert arb2.List_LC();
}

method Check_Set_l(x: QueueNode, l: QueueNode?, arb1: QueueNode, arb2: QueueNode)
    modifies x
{
    assume arb1.BST_LC();
    assume arb2.List_LC();
    assume arb1 != x.l;
    assume arb1 != x;
    x.l := l;
    assert arb1.BST_LC();
    assert arb2.List_LC();
}

method Check_Set_r(x: QueueNode, r: QueueNode?, arb1: QueueNode, arb2: QueueNode)
    modifies x
{
    assume arb1.BST_LC();
    assume arb2.List_LC();
    assume arb1 != x.r;
    assume arb1 != x;
    x.r := r;
    assert arb1.BST_LC();
    assert arb2.List_LC();
}

method Check_Set_p(x: QueueNode, p: QueueNode?, arb1: QueueNode, arb2: QueueNode)
    modifies x
{
    assume arb1.BST_LC();
    assume arb2.List_LC();
    assume arb1 != x.p;
    assume arb1 != x;
    assume x.p != null;
    x.p := p;
    assert arb1.BST_LC();
    assert arb2.List_LC();
}

method Check_Set_min(x: QueueNode, min: int, arb1: QueueNode, arb2: QueueNode)
    modifies x
{
    assume arb1.BST_LC();
    assume arb2.List_LC();
    assume arb1 != x.p;
    assume arb1 != x;
    x.min := min;
    assert arb1.BST_LC();
    assert arb2.List_LC();
}

method Check_Set_max(x: QueueNode, max: int, arb1: QueueNode, arb2: QueueNode)
    modifies x
{
    assume arb1.BST_LC();
    assume arb2.List_LC();
    assume arb1 != x.p;
    assume arb1 != x;
    x.max := max;
    assert arb1.BST_LC();
    assert arb2.List_LC();
}

method Check_Set_bst_keys(x: QueueNode, keys: set<int>, arb1: QueueNode, arb2: QueueNode)
    modifies x
{
    assume arb1.BST_LC();
    assume arb2.List_LC();
    assume arb1 != x.p;
    assume arb1 != x;
    x.bst_keys := keys;
    assert arb1.BST_LC();
    assert arb2.List_LC();
}

method Check_Set_bst_repr(x: QueueNode, repr: set<QueueNode>, arb1: QueueNode, arb2: QueueNode)
    modifies x
{
    assume arb1.BST_LC();
    assume arb2.List_LC();
    assume arb1 != x.p;
    assume arb1 != x;
    assume x.p != null;
    x.bst_repr := repr;
    assert arb1.BST_LC();
    assert arb2.List_LC();
}

method Check_Set_bst_depth(x: QueueNode, depth: nat, arb1: QueueNode, arb2: QueueNode)
    modifies x
{
    assume arb1.BST_LC();
    assume arb2.List_LC();
    assume arb1 != x.l;
    assume arb1 != x.r;
    assume arb1 != x;
    x.bst_depth := depth;
    assert arb1.BST_LC();
    assert arb2.List_LC();
}

method Check_Set_bst_root(x: QueueNode, root: QueueNode, arb1: QueueNode, arb2: QueueNode)
    modifies x
{
    assume arb1.BST_LC();
    assume arb2.List_LC();
    assume arb1 != x.l;
    assume arb1 != x.r;
    assume arb1 != x;
    assume arb2 != x;
    assume arb2 != x.prev;
    x.bst_root := root;
    assert arb1.BST_LC();
    assert arb2.List_LC();
}

method Check_DeleteFromRootRepr(x: QueueNode, node: QueueNode, arb: QueueNode)
    modifies x
{
    assume arb.LC();
    assume node.BST_Isolated();
    assume arb != x;
    assume x.p == null;
    x.bst_repr := x.bst_repr - {node};
    assert arb.LC();
}

method Check_Set_next(x: QueueNode, n: QueueNode?, arb1: QueueNode, arb2: QueueNode)
    modifies x
{
    assume arb1.BST_LC();
    assume arb2.List_LC();
    assume arb2 != x.next;
    assume arb2 != x;
    x.next := n;
    assert arb1.BST_LC();
    assert arb2.List_LC();
}

method Check_Set_prev(x: QueueNode, p: QueueNode?, arb1: QueueNode, arb2: QueueNode)
    modifies x
{
    assume arb1.BST_LC();
    assume arb2.List_LC();
    assume arb2 != x.prev;
    assume arb2 != x;
    x.prev := p;
    assert arb1.BST_LC();
    assert arb2.List_LC();
}

method Check_Set_list_keys(x: QueueNode, keys: set<int>, arb1: QueueNode, arb2: QueueNode)
    modifies x
{
    assume arb1.BST_LC();
    assume arb2.List_LC();
    assume arb2 != x.prev;
    assume arb2 != x;
    x.list_keys := keys;
    assert arb1.BST_LC();
    assert arb2.List_LC();
}

method Check_Set_list_repr(x: QueueNode, repr: set<QueueNode>, arb1: QueueNode, arb2: QueueNode)
    modifies x
{
    assume arb1.BST_LC();
    assume arb2.List_LC();
    assume arb2 != x.prev;
    assume arb2 != x;
    x.list_repr := repr;
    assert arb1.BST_LC();
    assert arb2.List_LC();
}
