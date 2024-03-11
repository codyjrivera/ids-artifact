// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions"
// by Anonymous Authors.
// 
// Artifact by Anonymous Author, 2023-2024. 
//
// Verification of Sorted List Find.

include "sorted-list.dfy"

method SortedListReverse(ghost Br: set<SortedNode>, x: SortedNode?, k: int)
    returns (ghost Br': set<SortedNode>, ret: SortedNode?)
    requires Br == {}
    requires x != null ==> x.LC() && x.sorted && x.prev == null
    modifies if x == null then {} else x.repr
    ensures ret == null <==> x == null
    ensures ret != null ==> (
        ret.LC() && ret.rev_sorted
        && ret.keys == old(x.keys)
        && ret.repr == old(x.repr)
        && ret.prev == null
    )
    ensures Br' == {}
{
    Br' := Br;
    var oldList := x;
    ret := null;

    while oldList != null
        invariant oldList != null ==> 
                        oldList.LC() 
                        && oldList.sorted && oldList.prev == null
        invariant ret != null ==> 
                        ret.LC() 
                        && ret.rev_sorted && ret.prev == null
        invariant oldList != null && ret != null ==>
                        ret.k <= oldList.k
        invariant x != null ==> (
            old(x.keys) == (if oldList == null then {} else oldList.keys)
                            + (if ret == null then {} else ret.keys)
            && old(x.repr) == (if oldList == null then {} else oldList.repr)
                                + (if ret == null then {} else ret.repr)
        )
        invariant (if oldList == null then {} else oldList.repr)
                !! (if ret == null then {} else ret.repr)
        invariant x == null ==> ret == null
        invariant Br' == {}
        decreases if oldList == null then {} else oldList.repr
    {
        var tmp := oldList.next;
        if tmp != null {
            IfNotBr_ThenLC(Br', tmp);
            Br' := tmp.Set_prev(Br', null);
        }
        Br' := oldList.Set_next(Br', ret);
        if ret != null {
            Br' := ret.Set_prev(Br', oldList);
        }
        Br' := oldList.Set_keys(Br', {oldList.k} + (if oldList.next == null then {} else oldList.next.keys));
        Br' := oldList.Set_repr(Br', {oldList} + (if oldList.next == null then {} else oldList.next.repr));
        Br' := oldList.Set_sorted(Br', false);
        Br' := oldList.Set_rev_sorted(Br', true);
        Br' := AssertLCAndRemove(Br', oldList);
        Br' := AssertLCAndRemove(Br', ret);
        Br' := AssertLCAndRemove(Br', tmp);
        ret := oldList;
        oldList := tmp;
    }
}
