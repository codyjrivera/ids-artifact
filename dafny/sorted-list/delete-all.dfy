// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions"
// by Anonymous Authors.
// 
// Artifact by Anonymous Author, 2023. 
//
// Verification of Sorted List Delete All.

include "sorted-list.dfy"

method SortedListDeleteAll(ghost Br: set<SortedNode>, x: SortedNode?, k: int)
    returns (ghost Br': set<SortedNode>, ret: SortedNode?)
    requires Br !! (if x == null then {} else x.repr)
    requires x != null ==> x.LC() && x.sorted && x.prev == null
    modifies if x == null then {} else x.repr
    decreases if x == null then {} else x.repr
    ensures x == null || old(x.keys) == {k} ==> ret == null
    ensures x != null && old(x.keys) != {} && old(x.keys) != {k} ==> ret != null
    ensures ret != null ==> (
        ret.LC()
        && ret.sorted
        && ret.k >= old(x.k)
        && ret.keys == old(x.keys) - {k}
        && ret.repr <= old(x.repr)
        && ret.prev == null
    )
    ensures Br' == Br
{
    Br' := Br;
    if x == null {
        ret := x;
    } else if x.k == k {
        var xn := x.next;
        if xn != null {
            IfNotBr_ThenLC(Br', xn);
        }
        Br' := x.Set_next(Br', null);
        if xn != null {
            Br' := xn.Set_prev(Br', null);
        }
        Br' := AssertLCAndRemove(Br', xn);
        Br' := x.Set_keys(Br', {x.k});
        Br' := x.Set_repr(Br', {x});
        Br' := AssertLCAndRemove(Br', x);
        var tmp;
        Br', tmp := SortedListDeleteAll(Br', xn, k);
        ret := tmp;
    } else {
        var xn := x.next;
        if xn != null {
            IfNotBr_ThenLC(Br', xn);
        }
        Br' := x.Set_next(Br', null);
        if xn != null {
            Br' := xn.Set_prev(Br', null);
        }
        Br' := AssertLCAndRemove(Br', xn);
        var tmp;
        Br', tmp := SortedListDeleteAll(Br', xn, k);
        Br' := x.Set_next(Br', tmp);
        if tmp != null {
            Br' := tmp.Set_prev(Br', x);
        }
        Br' := x.Set_keys(Br', {x.k} + (if x.next == null then {} else x.next.keys));
        Br' := x.Set_repr(Br', {x} + (if x.next == null then {} else x.next.repr));
        Br' := AssertLCAndRemove(Br', x);
        Br' := AssertLCAndRemove(Br', tmp);
        ret := x;
    }
}
