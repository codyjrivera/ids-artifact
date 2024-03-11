// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions"
// by Anonymous Authors.
// 
// Artifact by Anonymous Author, 2023. 
//
// Verification of RBT Find Min.

include "red-black-tree.dfy"

method RBTFindMin(ghost Br: set<RBTNode>, x: RBTNode)
    returns (ghost Br': set<RBTNode>, ret: int)
    requires Br !! x.repr
    requires x.LC()
    ensures ret in x.keys
    ensures ret == x.min
    ensures Br' == Br
{
    Br' := Br;
    var cur: RBTNode := x;
    while cur.l != null
        invariant cur.LC()
        invariant cur.keys <= x.keys
        invariant cur.min == x.min
        decreases cur.repr
    {
        IfNotBr_ThenLC(Br', cur.l);
        cur := cur.l;
    }
    ret := cur.k;
}