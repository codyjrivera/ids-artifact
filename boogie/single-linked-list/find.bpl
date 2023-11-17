// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions of Data Structures"
// by Anonymous Authors.
// 
// Artifact by Anonymous Author, 2023. 
//
// Verification of Single Linked List Find.

procedure SLLFindContract(x: Ref, k: int) returns (found: bool);
    requires RefSetsEqual(Br, EmptyRefSet);
    requires x != null ==> LC(C.k, C.next, C.prev, C.keys, C.repr, x);
    ensures found <==> x != null && (C.keys[x])[k];
    ensures !found <==> x == null || !(C.keys[x])[k];
    
procedure SLLFind(x: Ref, k: int) returns (found: bool)
    requires RefSetsEqual(Br, EmptyRefSet);
    requires x != null ==> LC(C.k, C.next, C.prev, C.keys, C.repr, x);
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
        call found := SLLFindContract(x_next, k);
    }
}