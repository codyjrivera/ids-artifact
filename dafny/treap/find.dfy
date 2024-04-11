// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions"
// by Adithya Murali, Cody Rivera, and P. Madhusudan.
// 
// Artifact by Cody Rivera, 2023-2024. 
//
// Verification of Treap Find.

include "treap.dfy"

method TreapLookup(ghost Br: set<TreapNode>, x: TreapNode?, k: int)
    returns (ret: TreapNode?)
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
            //TreapNotIn_Keyset(Br, x.r, k);
        }
        ret := TreapLookup(Br, x.l, k);
    } else {
        if (x.l != null) {
            IfNotBr_ThenLC(Br, x.l);
        }
        if (x.r != null) {
            IfNotBr_ThenLC(Br, x.r);
        }
        if (x.l != null) {
            //TreapNotIn_Keyset(Br, x.l, k);
        }
        ret := TreapLookup(Br, x.r, k);
    }
}

