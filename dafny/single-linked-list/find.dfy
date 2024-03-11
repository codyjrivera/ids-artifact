// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions"
// by Anonymous Authors.
// 
// Artifact by Anonymous Author, 2023. 
//
// Verification of SLL Find.

include "single-linked-list.dfy"

method SLLFind(ghost Br: set<SLLNode>, x: SLLNode?, k: int)
    returns (ghost Br': set<SLLNode>, found: bool)
    requires Br == {}
    requires x != null ==> x.LC()
    decreases if x == null then {} else x.repr
    ensures found <==> x != null && k in x.keys
    ensures !found <==> x == null || k !in x.keys
    ensures Br == {}
{
    Br' := Br;
    if x == null {
        found := false;
    } else if k == x.k {
        found := true;
    } else {
        if x.next != null {
            IfNotBr_ThenLC(Br', x.next);
        }
        Br', found := SLLFind(Br', x.next, k);
    }
}
