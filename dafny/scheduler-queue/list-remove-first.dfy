// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions"
// by Anonymous Authors.
// 
// Artifact by Anonymous Author, 2023. 
//
// Verification of Scheduler Queue List Remove First.

include "scheduler-queue.dfy"

method ListRemoveFirst(ghost Br: QueueBr, q: Queue, x: QueueNode?)
    returns (ghost Br': QueueBr, ret: QueueNode?, node: QueueNode?)
    requires Br.list == {} && Br.bst == {}
    requires x != null ==> x.LC() && x.prev == null
    modifies if x == null then {} else x.list_repr
    ensures x == null ==> ret == null
    ensures x != null ==> ret == old(x.next)
    ensures node == x
    ensures (ret != null ==>
                ret.LC()
                && ret.prev == null
                && ret.list_repr == old(x.list_repr) - {node}
                && ret.list_keys == old(x.list_keys) - {node.k}
                && ret.BST_FieldsUnchanged())
    ensures (node != null ==> 
                node.LC()
                && node.k == old(x.k)
                && node.next == null
                && node.prev == null
                && node.BST_FieldsUnchanged())
    ensures q.q1t != null ==> q.q1t.BST_FieldsUnchanged()
    ensures Br'.list == {} && Br'.bst == {}
{
    Br' := Br;
    if x == null {
        return Br', null, null;
    }
    if x.next != null {
        IfNotBr_ThenLC(Br', x.next);
    }
    node := x;
    ret := x.next;
    Br' := node.Set_prev(Br', null);
    Br' := node.Set_next(Br', null);
    Br' := node.Set_list_keys(Br', {node.k});
    Br' := node.Set_list_repr(Br', {node});
    if (ret != null) {
        Br' := ret.Set_prev(Br', null);
    }
    Br' := AssertLCAndRemove(Br', node);
    Br' := AssertLCAndRemove(Br', ret);
}
