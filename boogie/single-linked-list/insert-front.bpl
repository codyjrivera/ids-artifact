// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions"
// by Adithya Murali, Cody Rivera, and P. Madhusudan.
// 
// Artifact by Cody Rivera, 2023-2024. 
//
// Verification of Single Linked List Insert Front.

procedure SLLInsertFront(x: Ref, k: int) returns (ret: Ref)
    requires RefSetsEqual(Br, EmptyRefSet);
    requires LC(C.k, C.next, C.prev, C.keys, C.repr, x);
    modifies Br, alloc, C.k, C.next, C.prev, C.keys, C.repr;
    ensures RefSetSubset(old(alloc), alloc);
    ensures ret != null;
    ensures LC(C.k, C.next, C.prev, C.keys, C.repr, ret);
    ensures KeySetsEqual(C.keys[ret], (if x == null then EmptyKeySet else old(C.keys)[x])[k := true]);
    ensures Fresh(RefSetDiffF(C.repr[ret], (if x == null then EmptyRefSet else old(C.repr)[x])), alloc, old(alloc));
    ensures C.prev[ret] == null;
    ensures x != null ==> (ret == x || C.next[ret] == x);
    ensures (x == null || old(C.prev)[x] == null) ==> RefSetsEqual(Br, EmptyRefSet);
    ensures (x != null && old(C.prev)[x] != null) ==> RefSetsEqual(Br, EmptyRefSet[old(C.prev)[x] := true]);
    // Framing conditions.
    ensures Frame_all(C.k, C.next, C.prev, C.keys, C.repr,
                      old(C.k), old(C.next), old(C.prev), old(C.keys), old(C.repr),
                      if x == null then EmptyRefSet else old(C.repr)[x], old(alloc));
{
    // Local variables
    var head: Ref;

    // Subexpressions
    var head_next: Ref;
    var head_next_keys: KeySet;
    var head_next_repr: RefSet;
    var head_k: int;

    call InAllocParam(x);

    call head := Create(k);
    call Set_next(head, x);
    if (x != null) {
        call Set_prev(x, head);
    }
    call head_next := Get_next(head);
    call head_k := Get_k(head);
    if (head_next != null) {
        call head_next_keys := Get_keys(head_next);
        call head_next_repr := Get_repr(head_next);
    }
    call Set_keys(head, (if head_next == null then EmptyKeySet else head_next_keys)[head_k := true]);
    call Set_repr(head, (if head_next == null then EmptyRefSet else head_next_repr)[head := true]);

    call AssertLCAndRemove(head);
    call AssertLCAndRemove(x);

    ret := head;
}