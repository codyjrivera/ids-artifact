// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions"
// by Anonymous Authors.
// 
// Artifact by Anonymous Author, 2023. 
//
// Verification of SLL Insert Front.

include "single-linked-list.dfy"

method SLLInsertFront(ghost Br: set<SLLNode>, x: SLLNode?, k: int)
    returns (ghost Br': set<SLLNode>, ret: SLLNode)
    requires Br == {}
    requires x != null ==> x.LC()
    modifies x
    ensures ret.LC()
    ensures ret.keys == (if x == null then {} else old(x.keys)) + {k}
    ensures fresh(ret.repr - (if x == null then {} else old(x.repr)))
    ensures ret.prev == null
    ensures x == null || old(x.prev) == null ==> Br' == {}
    ensures x != null && old(x.prev) != null ==> Br' == {old(x.prev)}
{
    Br' := Br;
    var head;
    Br', head := SLLNode.Create(Br', k);
    Br' := head.Set_next(Br', x);
    if x != null {
        Br' := x.Set_prev(Br', head);
    }
    Br' := head.Set_keys(Br', {head.k} + (if head.next == null then {} else head.next.keys));
    Br' := head.Set_repr(Br', {head} + (if head.next == null then {} else head.next.repr));
    Br' := AssertLCAndRemove(Br', head);
    Br' := AssertLCAndRemove(Br', x);
    ret := head;
}
