// Supporting Artifact for
// "Predictive Verification using Intrinsic Definitions of Data Structures"
// by Adithya Murali, Cody Rivera, and P. Madhusudan.
// 
// Artifact by Cody Rivera, 2023. 
//
// Verification of Single-Linked List Append (destructive).

procedure SLLAppendContract(x1: Ref, x2: Ref) returns (ret: Ref);
    requires RefSetsEqual(Br, EmptyRefSet);
    requires x1 != null ==> (
        LC(C.k, C.next, C.prev, 
            C.keys, C.repr, x1) 
    );
    requires x2 != null ==> (
        LC(C.k, C.next, C.prev, 
            C.keys, C.repr, x2)
        && C.prev[x2] == null  
    );
    requires x1 != null && x2 != null ==> 
                    RefSetsDisjoint(C.repr[x1], C.repr[x2]);
    modifies Br, C.k, C.next, C.prev, C.keys, C.repr;
    ensures x1 == null && x2 == null ==> ret == null;
    ensures x1 != null || x2 != null ==> ret != null;
    ensures ret != null ==> (
        LC(C.k, C.next, C.prev, 
            C.keys, C.repr, ret)
        && KeySetsEqual(
                C.keys[ret],
                KeySetUnionF(
                    if x1 == null then EmptyKeySet else old(C.keys)[x1],
                    if x2 == null then EmptyKeySet else old(C.keys)[x2]
                )
            )
        && RefSetsEqual(
                C.repr[ret],
                RefSetUnionF(
                    if x1 == null then EmptyRefSet else old(C.repr)[x1],
                    if x2 == null then EmptyRefSet else old(C.repr)[x2]
                )
            )
        && C.prev[ret] == null
        && (ret == x1 || ret == x2)
        && (x1 != null ==> ret == x1)
    );
    ensures x1 == null || (x1 != null && old(C.prev)[x1] == null) ==> RefSetsEqual(Br, EmptyRefSet);
    ensures x1 != null && old(C.prev)[x1] != null ==> RefSetsEqual(Br, EmptyRefSet[old(C.prev)[x1] := true]);
    // Framing conditions.
    ensures Frame_all(
        C.k, C.next, C.prev, 
        C.keys, C.repr,
        old(C.k), old(C.next), old(C.prev),
        old(C.keys), old(C.repr),
        RefSetUnionF(
            if x1 == null then EmptyRefSet else old(C.repr)[x1],
            if x2 == null then EmptyRefSet else EmptyRefSet[x2 := true]
        ), 
        old(alloc)
    );

procedure SLLAppend(x1: Ref, x2: Ref) returns (ret: Ref)
    requires RefSetsEqual(Br, EmptyRefSet);
    requires x1 != null ==> (
        LC(C.k, C.next, C.prev, 
            C.keys, C.repr, x1) 
    );
    requires x2 != null ==> (
        LC(C.k, C.next, C.prev, 
            C.keys, C.repr, x2)
        && C.prev[x2] == null  
    );
    requires x1 != null && x2 != null ==> 
                    RefSetsDisjoint(C.repr[x1], C.repr[x2]);
    modifies Br, C.k, C.next, C.prev, C.keys, C.repr;
    ensures x1 == null && x2 == null ==> ret == null;
    ensures x1 != null || x2 != null ==> ret != null;
    ensures ret != null ==> (
        LC(C.k, C.next, C.prev, 
            C.keys, C.repr, ret)
        && KeySetsEqual(
                C.keys[ret],
                KeySetUnionF(
                    if x1 == null then EmptyKeySet else old(C.keys)[x1],
                    if x2 == null then EmptyKeySet else old(C.keys)[x2]
                )
            )
        && RefSetsEqual(
                C.repr[ret],
                RefSetUnionF(
                    if x1 == null then EmptyRefSet else old(C.repr)[x1],
                    if x2 == null then EmptyRefSet else old(C.repr)[x2]
                )
            )
        && C.prev[ret] == null
        && (ret == x1 || ret == x2)
        && (x1 != null ==> ret == x1)
    );
    ensures x1 == null || (x1 != null && old(C.prev)[x1] == null) ==> RefSetsEqual(Br, EmptyRefSet);
    ensures x1 != null && old(C.prev)[x1] != null ==> RefSetsEqual(Br, EmptyRefSet[old(C.prev)[x1] := true]);
    // Framing conditions.
    ensures Frame_all(
        C.k, C.next, C.prev, 
        C.keys, C.repr,
        old(C.k), old(C.next), old(C.prev),
        old(C.keys), old(C.repr),
        RefSetUnionF(
            if x1 == null then EmptyRefSet else old(C.repr)[x1],
            if x2 == null then EmptyRefSet else EmptyRefSet[x2 := true]
        ), 
        old(alloc)
    );
{
    // Local variables
    var x1n: Ref;
    var tmp: Ref;

    // Subexpressions
    var x1_k: int;
    var x1_next: Ref;
    var x1_next_keys: KeySet; var x1_next_repr: RefSet;
    
    call InAllocParam(x1);
    call InAllocParam(x2);

    if (x1 == null) {
        ret := x2;
    } else {
        call x1n := Get_next(x1);
        call IfNotBr_ThenLC(x1n);

        call tmp := SLLAppendContract(x1n, x2);
        call Set_next(x1, tmp);
        if (tmp != null) {
            call Set_prev(tmp, x1);
        }
        
        call x1_k := Get_k(x1);
        call x1_next := Get_next(x1);
        if (x1_next != null) {
            call x1_next_keys := Get_keys(x1_next);
            call x1_next_repr := Get_repr(x1_next);
        }
        call Set_keys(
            x1, 
            (if x1_next == null then EmptyKeySet else x1_next_keys)[x1_k := true]
        );
        call Set_repr(
            x1, 
            (if x1_next == null then EmptyRefSet else x1_next_repr)[x1 := true]
        );
        call Set_prev(x1, null);

        call AssertLCAndRemove(x1);
        call AssertLCAndRemove(tmp);

        ret := x1;
    }
}
