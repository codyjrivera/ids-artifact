// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions"
// by Adithya Murali, Cody Rivera, and P. Madhusudan.
// 
// Artifact by Cody Rivera, 2023-2024. 
//
// Verification of SLL Insert Back.

include "single-linked-list.dfy"

method SLLInsertBack(ghost Br: set<SLLNode>, x: SLLNode?, k: int)
    returns (ghost Br': set<SLLNode>, ret: SLLNode)
    requires Br == {}
    requires x != null ==> x.LC()
    modifies if x == null then {} else x.repr
    decreases if x == null then {} else x.repr
    ensures ret.LC()
    ensures ret.keys == (if x == null then {} else old(x.keys)) + {k}
    ensures fresh(ret.repr - (if x == null then {} else old(x.repr)))
    ensures ret.prev == null
    ensures x != null ==> ret == x
    ensures x == null || old(x.prev) == null ==> Br' == {}
    ensures x != null && old(x.prev) != null ==> Br' == {old(x.prev)}
{
    Br' := Br;
    if x == null {
        var tail;
        Br', tail := SLLNode.Create(Br', k);
        Br' := tail.Set_keys(Br', {k});
        Br' := tail.Set_repr(Br', {tail});
        Br' := AssertLCAndRemove(Br', tail);
        ret := tail;
    } else {
        var tmp;
        if x.next != null {
            IfNotBr_ThenLC(Br', x.next);
        }
        Br', tmp := SLLInsertBack(Br', x.next, k);
        Br' := x.Set_next(Br', tmp);
        Br' := tmp.Set_prev(Br', x);
        Br' := x.Set_keys(Br', {x.k} + (if x.next == null then {} else x.next.keys));
        Br' := x.Set_repr(Br', {x} + (if x.next == null then {} else x.next.repr));
        Br' := x.Set_prev(Br', null);
        Br' := AssertLCAndRemove(Br', tmp);
        Br' := AssertLCAndRemove(Br', x);
        ret := x;
    }
}
