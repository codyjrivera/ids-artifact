// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions"
// by Adithya Murali, Cody Rivera, and P. Madhusudan.
// 
// Artifact by Cody Rivera, 2023-2024. 
//
// Verification of SLL Reverse.

include "single-linked-list.dfy"

method SLLReverse(ghost Br: set<SLLNode>, x: SLLNode?, k: int)
    returns (ghost Br': set<SLLNode>, ret: SLLNode?)
    requires Br == {}
    requires x != null ==> x.LC() && x.prev == null
    modifies if x == null then {} else x.repr
    ensures ret == null <==> x == null
    ensures ret != null ==> (
        ret.LC()
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
        invariant oldList != null ==> oldList.LC() && oldList.prev == null
        invariant ret != null ==> ret.LC() && ret.prev == null
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
        Br' := AssertLCAndRemove(Br', oldList);
        Br' := AssertLCAndRemove(Br', ret);
        Br' := AssertLCAndRemove(Br', tmp);
        ret := oldList;
        oldList := tmp;
    }
 
}
