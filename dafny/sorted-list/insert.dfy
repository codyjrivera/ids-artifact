// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions"
// by Anonymous Authors.
// 
// Artifact by Anonymous Author, 2023. 
//
// Verification of Sorted List Insert.

include "sorted-list.dfy"

method SortedListInsert(ghost Br: set<SortedNode>, x: SortedNode?, k: int)
    returns (ghost Br': set<SortedNode>, ret: SortedNode)
    requires Br == {}
    requires x != null ==> x.LC() && x.sorted
    modifies if x == null then {} else x.repr
    decreases if x == null then {} else x.repr
    ensures ret.LC() && ret.sorted
    // The new "first key" is the minimum of the old "first key" and k
    ensures ret.k == (if x != null && old(x.k) <= k then old(x.k) else k)
    ensures ret.keys == (if x == null then {} else old(x.keys)) + {k}
    ensures fresh(ret.repr - (if x == null then {} else old(x.repr)))
    ensures ret.prev == null
    ensures x != null ==> ret == x || ret.next == x
    ensures x == null || old(x.prev) == null ==> Br' == {}
    ensures x != null && old(x.prev) != null ==> Br' == {old(x.prev)}
{
    Br' := Br;
    if x == null {
        var node;
        Br', node := SortedNode.Create(Br', k);
        Br' := node.Set_next(Br', null);
        
        Br' := node.Set_prev(Br', null);
        Br' := node.Set_keys(Br', {k});
        Br' := node.Set_repr(Br', {node});
        Br' := node.Set_sorted(Br', true);
        Br' := node.Set_rev_sorted(Br', false);

        Br' := AssertLCAndRemove(Br', node);
        ret := node;
    } else if k <= x.k {
        var node;
        Br', node := SortedNode.Create(Br', k);
        Br' := node.Set_next(Br', x);

        Br' := node.Set_prev(Br', null);
        Br' := node.Set_keys(Br', {node.k} + (if node.next == null then {} else node.next.keys));
        Br' := node.Set_repr(Br', {node} + (if node.next == null then {} else node.next.repr));
        Br' := node.Set_sorted(Br', true);
        Br' := node.Set_rev_sorted(Br', false);
        Br' := x.Set_prev(Br', node);

        Br' := AssertLCAndRemove(Br', x);
        Br' := AssertLCAndRemove(Br', node);
        ret := node;
    } else {
        if x.next != null {
            IfNotBr_ThenLC(Br', x.next);
        }

        var tmp;
        Br', tmp := SortedListInsert(Br', x.next, k);
        if x.next != null {
            IfNotBr_ThenLC(Br', x.next);
        }

        var oldnext := x.next;
        Br' := tmp.Set_prev(Br', x);
        Br' := x.Set_next(Br', tmp);
        Br' := AssertLCAndRemove(Br', tmp);
        Br' := AssertLCAndRemove(Br', oldnext);
        
        Br' := x.Set_keys(Br', {x.k} + (if x.next == null then {} else x.next.keys));
        Br' := x.Set_repr(Br', {x} + (if x.next == null then {} else x.next.repr));
        Br' := x.Set_prev(Br', null);

        Br' := AssertLCAndRemove(Br', x);
        ret := x;
    }
}
