// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions"
// by Anonymous Authors.
// 
// Artifact by Anonymous Author, 2023. 
//
// Verification of AVL Tree Find Min.

include "avl-tree.dfy"

method AVLFindMin(ghost Br: set<AVLNode>, x: AVLNode)
    returns (ghost Br': set<AVLNode>, ret: int)
    requires Br !! x.repr
    requires x.LC()
    ensures ret in x.keys
    ensures ret == x.min
    ensures Br' == Br
{
    Br' := Br;
    var cur: AVLNode := x;
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