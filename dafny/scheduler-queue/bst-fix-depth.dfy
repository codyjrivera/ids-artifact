// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions"
// by Anonymous Authors.
// 
// Artifact by Anonymous Author, 2023. 
//
// Verification of Scheduler Queue Fix Depth.

include "scheduler-queue.dfy"

ghost method BSTFixDepth(Br: QueueBr, q: Queue, x: QueueNode)
    returns (Br': QueueBr)
    requires (x.bst_repr - {x}) !! Br.bst && Br.list == {}
    requires x.LC_Trans_NoDepth() && x.p != null
    modifies x.bst_repr * x.bst_root.bst_repr
    decreases x.bst_repr
    ensures x.LC()
    ensures x.k == old(x.k)
    ensures x.l == old(x.l)
    ensures x.r == old(x.r)
    ensures x.p == old(x.p)
    ensures x.min == old(x.min)
    ensures x.max == old(x.max)
    ensures x.bst_keys == old(x.bst_keys)
    ensures x.bst_repr == old(x.bst_repr)
    ensures x.bst_root == old(x.bst_root)
    ensures x.List_FieldsUnchanged()
    ensures q.q1s != null ==> q.q1s.List_FieldsUnchanged() && q.q1s.bst_root == old(q.q1s.bst_root)
    ensures Br'.bst == Br.bst - {x}
    ensures Br'.list == {}
{
    Br' := Br;
    if x.l != null {
        IfNotBr_ThenLC(Br', x.l);
    }
    if x.r != null {
        IfNotBr_ThenLC(Br', x.r);
    }
    Br' := x.Set_bst_depth(Br', 1 + x.p.bst_depth);
    Br' := AssertLCAndRemove(Br', x);

    if x.l != null {
        Br' := BSTFixDepth(Br', q, x.l);
    }
    if x.r != null {
        IfNotBrList_ThenList_LC(Br', x.r);
        Br' := BSTFixDepth(Br', q, x.r);
    }
    IfNotBrList_ThenList_LC(Br', x);
}
