// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions of Datastructures"
// by Anonymous Authors.
// 
// Artifact by Anonymous Author, 2023. 
//
// Verification of Sorted List Find.

procedure SortedListFindContract(x: Ref, k: int) returns (found: bool);
    requires RefSetsEqual(Br, EmptyRefSet);
    requires x != null ==> LC(C.k, C.next, C.prev, C.keys, C.repr, C.sorted, C.rev_sorted, x);
    ensures found <==> x != null && (C.keys[x])[k];
    ensures !found <==> x == null || !(C.keys[x])[k];
    
procedure SortedListFind(x: Ref, k: int) returns (found: bool)
    requires RefSetsEqual(Br, EmptyRefSet);
    requires x != null ==> LC(C.k, C.next, C.prev, C.keys, C.repr, C.sorted, C.rev_sorted, x);
    ensures found <==> x != null && (C.keys[x])[k];
    ensures !found <==> x == null || !(C.keys[x])[k];
{
    var x_k: int;
    var x_next: Ref;

    call InAllocParam(x);

    if (x != null) {
        call x_k := Get_k(x);
        call x_next := Get_next(x);
    }
    if (x == null) {
        found := false;
    } else if (k == x_k) {
        found := true;
    } else {
        call IfNotBr_ThenLC(x_next);
        call found := SortedListFindContract(x_next, k);
    }
}
