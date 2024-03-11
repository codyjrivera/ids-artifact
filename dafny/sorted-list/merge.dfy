// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions"
// by Anonymous Authors.
// 
// Artifact by Anonymous Author, 2023-2024. 
//
// Verification of Sorted List Find.

include "sorted-list.dfy"

method SortedListMerge(ghost Br: set<SortedNode>, x1: SortedNode?, x2: SortedNode?)
    returns (ghost Br': set<SortedNode>, ret: SortedNode?)
    requires Br !! ((if x1 == null then {} else x1.repr) + (if x2 == null then {} else x2.repr))
    requires x1 != null ==> x1.LC() && x1.sorted && x1.prev == null
    requires x2 != null ==> x2.LC() && x2.sorted && x2.prev == null
    requires (if x1 == null then {} else x1.repr) !! (if x2 == null then {} else x2.repr)
    modifies if x1 == null then {} else x1.repr
    modifies if x2 == null then {} else x2.repr
    decreases if x1 == null then {} else x1.repr
    decreases if x2 == null then {} else x2.repr
    ensures ret == null <==> x1 == null && x2 == null
    ensures ret != null ==> (
        ret.LC() && ret.sorted
        && (x1 == null ==> ret.k == old(x2.k))
        && (x2 == null ==> ret.k == old(x1.k))
        && (x1 != null && x2 != null ==> ret.k == if old(x1.k) <= old(x2.k) then old(x1.k) else old(x2.k))
        && ret.prev == null
        && ret.keys == (if x1 == null then {} else old(x1.keys))
                        + (if x2 == null then {} else old(x2.keys))
        && ret.repr == (if x1 == null then {} else old(x1.repr))
                        + (if x2 == null then {} else old(x2.repr))
    )
    ensures Br' == Br
{
    Br' := Br;
    if x1 == null {
        ret := x2;
    } else if x2 == null {
        ret := x1;
    } else {
        if x1.k <= x2.k {
            var x1n := x1.next;
            if x1n != null {
                IfNotBr_ThenLC(Br', x1n);
            }
            
            Br' := x1.Set_next(Br', null);
            if x1n != null {
                Br' := x1n.Set_prev(Br', null);
            }
            Br' := AssertLCAndRemove(Br', x1n);

            var tl;
            Br', tl := SortedListMerge(Br', x1n, x2);
            Br' := x1.Set_next(Br', tl);

            Br' := x1.Set_keys(Br', {x1.k} + (if x1.next == null then {} else x1.next.keys));
            Br' := x1.Set_repr(Br', {x1} + (if x1.next == null then {} else x1.next.repr));
            if tl != null {
                Br' := tl.Set_prev(Br', x1);
            }

            Br' := AssertLCAndRemove(Br', x1);
            Br' := AssertLCAndRemove(Br', tl);

            ret := x1;
        } else {
            var x2n := x2.next;
            if x2n != null {
                IfNotBr_ThenLC(Br', x2n);
            }
            
            Br' := x2.Set_next(Br', null);
            if x2n != null {
                Br' := x2n.Set_prev(Br', null);
            }
            Br' := AssertLCAndRemove(Br', x2n);

            var tl;
            Br', tl := SortedListMerge(Br', x1, x2n);
            Br' := x2.Set_next(Br', tl);

            Br' := x2.Set_keys(Br', {x2.k} + (if x2.next == null then {} else x2.next.keys));
            Br' := x2.Set_repr(Br', {x2} + (if x2.next == null then {} else x2.next.repr));
            if tl != null {
                Br' := tl.Set_prev(Br', x2);
            }

            Br' := AssertLCAndRemove(Br', x2);
            Br' := AssertLCAndRemove(Br', tl);

            ret := x2;
        }
    }
}