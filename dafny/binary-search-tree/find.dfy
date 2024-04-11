// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions"
// by Adithya Murali, Cody Rivera, and P. Madhusudan.
// 
// Artifact by Cody Rivera, 2023-2024. 
//
// Verification of BST Find.

include "binary-search-tree.dfy"

method BSTLookup(ghost Br: set<BSTNode>, x: BSTNode?, k: int)
    returns (ret: BSTNode?)
    requires Br == {}
    requires x != null ==> x.LC()
    decreases if x == null then {} else x.repr
    //ensures x == null || k !in x.keys ==> ret == null
    //ensures x != null && k in x.keys ==> ret != null
    ensures (ret != null ==>
                ret.LC()
                && ret.k == k
                && x != null
                && k in x.keys)
{
    if x == null || k == x.k {
        return x;
    } else if k < x.k {
        if (x.l != null) {
            IfNotBr_ThenLC(Br, x.l);
        }
        if (x.r != null) {
            IfNotBr_ThenLC(Br, x.r);
        }
        if (x.r != null) {
            //BSTNotIn_Keyset(Br, x.r, k);
        }
        ret := BSTLookup(Br, x.l, k);
    } else {
        if (x.l != null) {
            IfNotBr_ThenLC(Br, x.l);
        }
        if (x.r != null) {
            IfNotBr_ThenLC(Br, x.r);
        }
        if (x.l != null) {
            //BSTNotIn_Keyset(Br, x.l, k);
        }
        ret := BSTLookup(Br, x.r, k);
    }
}

