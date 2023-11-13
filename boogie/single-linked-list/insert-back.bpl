// Supporting Artifact for
// "Predictive Verification using Intrinsic Definitions of Data Structures"
// by Adithya Murali, Cody Rivera, and P. Madhusudan.
// 
// Artifact by Cody Rivera, 2023. 
//
// Verification of Single Linked List Insert Back.

procedure SLLInsertBackContract(x: Ref, k: int) returns (ret: Ref);
    requires RefSetsEqual(Br, EmptyRefSet);
    requires LC(C.k, C.next, C.prev, C.keys, C.repr, x);
    modifies Br, alloc, C.k, C.next, C.prev, C.keys, C.repr;
    ensures RefSetSubset(old(alloc), alloc);
    ensures ret != null;
    ensures LC(C.k, C.next, C.prev, C.keys, C.repr, ret);
    ensures KeySetsEqual(C.keys[ret], (if x == null then EmptyKeySet else old(C.keys)[x])[k := true]);
    ensures Fresh(RefSetDiffF(C.repr[ret], (if x == null then EmptyRefSet else old(C.repr)[x])), alloc, old(alloc));
    ensures C.prev[ret] == null;
    ensures x != null ==> ret == x;
    ensures (x == null || old(C.prev)[x] == null) ==> RefSetsEqual(Br, EmptyRefSet);
    ensures (x != null && old(C.prev)[x] != null) ==> RefSetsEqual(Br, EmptyRefSet[old(C.prev)[x] := true]);
    // Framing conditions.
    ensures Frame_all(C.k, C.next, C.prev, C.keys, C.repr,
                      old(C.k), old(C.next), old(C.prev), old(C.keys), old(C.repr),
                      if x == null then EmptyRefSet else old(C.repr)[x], old(alloc));

procedure SLLInsertBack(x: Ref, k: int) returns (ret: Ref)
    requires RefSetsEqual(Br, EmptyRefSet);
    requires LC(C.k, C.next, C.prev, C.keys, C.repr, x);
    modifies Br, alloc, C.k, C.next, C.prev, C.keys, C.repr;
    ensures RefSetSubset(old(alloc), alloc);
    ensures ret != null;
    ensures LC(C.k, C.next, C.prev, C.keys, C.repr, ret);
    ensures KeySetsEqual(C.keys[ret], (if x == null then EmptyKeySet else old(C.keys)[x])[k := true]);
    ensures Fresh(RefSetDiffF(C.repr[ret], (if x == null then EmptyRefSet else old(C.repr)[x])), alloc, old(alloc));
    ensures C.prev[ret] == null;
    ensures x != null ==> ret == x;
    ensures (x == null || old(C.prev)[x] == null) ==> RefSetsEqual(Br, EmptyRefSet);
    ensures (x != null && old(C.prev)[x] != null) ==> RefSetsEqual(Br, EmptyRefSet[old(C.prev)[x] := true]);
    // Framing conditions.
    ensures Frame_all(C.k, C.next, C.prev, C.keys, C.repr,
                      old(C.k), old(C.next), old(C.prev), old(C.keys), old(C.repr),
                      if x == null then EmptyRefSet else old(C.repr)[x], old(alloc));
{
    // Local variables
    var tail: Ref;
    var tmp: Ref;

    // Subexpressions
    var x_next: Ref;
    var x_next_keys: KeySet;
    var x_next_repr: RefSet;
    var x_k: int;

    call InAllocParam(x);

    if (x == null) {
        call tail := Create(k);
        call Set_keys(tail, EmptyKeySet[k := true]);
        call Set_repr(tail, EmptyRefSet[tail := true]);
        call AssertLCAndRemove(tail);
        ret := tail;
    } else {
        call x_next := Get_next(x);
        call IfNotBr_ThenLC(x_next);
        call tmp := SLLInsertBackContract(x_next, k);
        call Set_next(x, tmp);
        call Set_prev(tmp, x);

        call x_next := Get_next(x);
        call x_k := Get_k(x);
        if (x_next != null) {
            call x_next_keys := Get_keys(x_next);
            call x_next_repr := Get_repr(x_next);
        }
        call Set_keys(x, (if x_next == null then EmptyKeySet else x_next_keys)[x_k := true]);
        call Set_repr(x, (if x_next == null then EmptyRefSet else x_next_repr)[x := true]);
        call Set_prev(x, null);

        call AssertLCAndRemove(tmp);
        call AssertLCAndRemove(x);
        ret := x;
    }
}