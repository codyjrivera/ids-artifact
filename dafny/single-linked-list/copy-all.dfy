// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions"
// by Anonymous Authors.
// 
// Artifact by Anonymous Author, 2023-2024. 
//
// Verification of SLL Copy All.

include "single-linked-list.dfy"

method SLLCopyAll(ghost Br: set<SLLNode>, x: SLLNode?)
    returns (ghost Br': set<SLLNode>, ret: SLLNode?)
    requires Br == {}
    requires x != null ==> x.LC()
    decreases if x == null then {} else x.repr
    ensures ret == null <==> x == null
    ensures ret != null ==> (
        ret.LC()
        && ret.keys == old(x.keys)
        && fresh(ret.repr)
        && ret.repr !! x.repr
        && ret.prev == null
    )
    ensures Br == {}
{
    Br' := Br;
    if x == null {
        ret := x;
    } else {
        var tmp, newNode;
        if x.next != null {
            IfNotBr_ThenLC(Br', x.next);
        }
        Br', tmp := SLLCopyAll(Br', x.next);
        Br', newNode := SLLNode.Create(Br', x.k);
        Br' := newNode.Set_next(Br', tmp);
        if tmp != null {
            Br' := tmp.Set_prev(Br', newNode);
        }
        Br' := newNode.Set_keys(Br', {newNode.k} + (if newNode.next == null then {} else newNode.next.keys));
        Br' := newNode.Set_repr(Br', {newNode} + (if newNode.next == null then {} else newNode.next.repr));
        Br' := newNode.Set_prev(Br', null);
        Br' := AssertLCAndRemove(Br', tmp);
        Br' := AssertLCAndRemove(Br', newNode);
        ret := newNode;
    }
}
