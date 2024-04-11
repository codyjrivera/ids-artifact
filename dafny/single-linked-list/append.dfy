// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions"
// by Adithya Murali, Cody Rivera, and P. Madhusudan.
// 
// Artifact by Cody Rivera, 2023-2024. 
//
// Verification of SLL Append.

include "single-linked-list.dfy"

method SLLAppend(ghost Br: set<SLLNode>, x1: SLLNode?, x2: SLLNode?)
    returns (ghost Br': set<SLLNode>, ret: SLLNode?)
    requires Br == {}
    requires x1 != null ==> x1.LC()
    requires x2 != null ==> x2.LC() && x2.prev == null
    requires x1 != null && x2 != null ==> x1.repr !! x2.repr
    modifies (if x1 == null then {} else x1.repr), x2
    decreases if x1 == null then {} else x1.repr
    ensures x1 == null && x2 == null ==> ret == null
    ensures x1 != null || x2 != null ==> ret != null
    ensures ret != null ==> (
        ret.LC()
        && ret.keys == 
            (if x1 == null then {} else old(x1.keys))
            + (if x2 == null then {} else old(x2.keys))
        && ret.repr ==
            (if x1 == null then {} else old(x1.repr))
            + (if x2 == null then {} else old(x2.repr))
        && ret.prev == null
        && (ret == x1 || ret == x2)
        && (x1 != null ==> ret == x1)
    )
    ensures x1 == null || (x1 != null && old(x1.prev) == null) ==> Br' == {}
    ensures x1 != null && old(x1.prev) != null ==> Br' == {old(x1.prev)}
{
    Br' := Br;
    if x1 == null {
        ret := x2;
        return;
    } else {
        var tmp;
        if x1.next != null {
            IfNotBr_ThenLC(Br', x1.next);
        }
        Br', tmp := SLLAppend(Br', x1.next, x2);
        Br' := x1.Set_next(Br', tmp);
        if tmp != null {
            Br' := tmp.Set_prev(Br', x1);
        }
        Br' := x1.Set_keys(Br', {x1.k} + (if x1.next == null then {} else x1.next.keys));
        Br' := x1.Set_repr(Br', {x1} + (if x1.next == null then {} else x1.next.repr));
        Br' := x1.Set_prev(Br', null);
        Br' := AssertLCAndRemove(Br', x1);
        Br' := AssertLCAndRemove(Br', tmp);
        ret := x1;
    }
}
