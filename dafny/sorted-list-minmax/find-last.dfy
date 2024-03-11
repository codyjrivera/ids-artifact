// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions"
// by Anonymous Authors.
// 
// Artifact by Anonymous Author, 2023. 
//
// Verification of Sorted List (with min/max) Find Last.

include "sorted-list-minmax.dfy"

method SortedListFindLast(ghost Br: set<SortedNode>, x: SortedNode)
    returns (ghost Br': set<SortedNode>, ret: SortedNode)
    requires Br == {}
    requires x.LC() && x.sorted
    ensures ret.LC() && ret.sorted
    ensures ret.next == null
    ensures ret in x.repr && ret.k in x.keys
    ensures ret.k == x.max
    ensures Br' == {}
{
    Br' := Br;

    var cur: SortedNode := x;
    while cur.next != null
        invariant cur.LC() && cur.sorted
        invariant cur.repr <= x.repr
        invariant cur.keys <= x.keys
        invariant cur.max == x.max
        decreases cur.repr
    {
        IfNotBr_ThenLC(Br', cur.next);
        cur := cur.next;
    }

    ret := cur;
}
