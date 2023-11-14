// Supporting Artifact for
// "Predictive Verification using Intrinsic Definitions of Data Structures"
// by Adithya Murali, Cody Rivera, and P. Madhusudan.
// 
// Artifact by Cody Rivera, 2023. 
//
// Verification of Circular List Delete Front.

// Deletes from the front of a circular list.
// 
// -> [x: last] -> [x.next] -> [x.next.next] ->
//          ==>
// -> [x: last] -> [x.next.next] ->

procedure CircularDeleteFront(x: Ref, k: int)
    requires x != null;
    requires RefSetsEqual(Br, EmptyRefSet);
    requires LC(C.k, C.next, C.prev,
                C.last, C.len, C.rlen, 
                C.keys, C.repr, x);
    requires C.last[x] == x;
    requires C.next[x] != x;
    modifies Br, C.k, C.next, C.prev,
                C.last, C.len, C.rlen, 
                C.keys, C.repr;
    ensures LC(C.k, C.next, C.prev,
                C.last, C.len, C.rlen, 
                C.keys, C.repr, x);
    ensures C.last[x] == x;
    ensures (KeySetsEqual(C.keys[C.last[x]], old(C.keys)[old(C.last)[x]])
                || KeySetsEqual(C.keys[C.last[x]], (old(C.keys)[old(C.last)[x]])[old(C.k)[old(C.next)[x]] := false]));
    ensures RefSetSubset(C.repr[C.last[x]], old(C.repr)[old(C.last)[x]]);
    ensures RefSetsEqual(Br, EmptyRefSet);
    // Framing conditions.
    ensures Frame_all(
        C.k, C.next, C.prev,
        C.last, C.len, C.rlen, 
        C.keys, C.repr,
        old(C.k), old(C.next), old(C.prev),
        old(C.last), old(C.len), old(C.rlen), 
        old(C.keys), old(C.repr),
        old(C.repr)[old(C.last)[x]], 
        old(alloc)
    );
{
    // Local variables
    var next: Ref;
    var cur: Ref;

    // Subexpressions
    var x_last: Ref;
    var next_next: Ref;
    var next_next_next: Ref;
    var x_next: Ref;
    var next_k: int;
    var x_next_keys: KeySet;
    var cur_next: Ref;
    var cur_prev: Ref; var cur_prev_rlen: int;

    // Saved pre-loop state
    var C.k_pl1: [Ref]int;
    var C.next_pl1: [Ref]Ref;
    var C.prev_pl1: [Ref]Ref;
    var C.last_pl1: [Ref]Ref;
    var C.len_pl1: [Ref]int;
    var C.rlen_pl1: [Ref]int;
    var C.keys_pl1: [Ref]KeySet;
    var C.repr_pl1: [Ref]RefSet;

    // Loop termination
    var t: int;
    var z: int;

    call InAllocParam(x);
    call x_last := Get_last(x);
    call InAllocParam(x_last);

    call next := Get_next(x);
    call IfNotBr_ThenLC(next);
    call next_next := Get_next(next);
    call IfNotBr_ThenLC(next_next);
    call next_next_next := Get_next(next_next);
    call IfNotBr_ThenLC(next_next_next);

    call Set_next(x, next_next);
    call Set_next(next, next);

    // repairing 'next'
    call Set_prev(next, next);
    call Set_len(next, 0);
    call Set_rlen(next, 0);
    call Set_keys(next, EmptyKeySet);
    call Set_repr(next, EmptyRefSet[next := true]);
    call Set_last(next, next);

    // repairing 'x'
    call x_next := Get_next(x);
    call Set_prev(x_next, x);
    call DeleteFromLastRepr(x, next);
    call next_k := Get_k(next);
    call x_next_keys := Get_keys(x_next);
    if (!x_next_keys[next_k] || x_next == x) {
        call DeleteFromLastKeys(x, next_k);
    }

    assert LC(C.k, C.next, C.prev,
                C.last, C.len, C.rlen, 
                C.keys, C.repr, x);
    assert LC(C.k, C.next, C.prev,
                C.last, C.len, C.rlen, 
                C.keys, C.repr, next);
    call AssertLCAndRemove(x);
    call AssertLCAndRemove(next);

    // Save ghost loop state
    C.k_pl1 := C.k;
    C.next_pl1 := C.next;
    C.prev_pl1 := C.prev;
    C.last_pl1 := C.last;
    C.len_pl1 := C.len;
    C.rlen_pl1 := C.rlen;
    C.keys_pl1 := C.keys;
    C.repr_pl1 := C.repr;
    
    call cur := Get_next(x);
    call cur_next := Get_next(cur);
    call IfNotBr_ThenLC(cur_next);
    while (cur != x)
        invariant cur != null;
        invariant cur_next == C.next[cur];
        invariant cur != x ==> (
            RefSetsEqual(Br, EmptyRefSet[cur := true])
            && LC_Trans_NoRlen(C.k, C.next, C.prev,
                C.last, C.len, C.rlen, 
                C.keys, C.repr, cur)
            && C.last[cur] == x
            && C.len[cur] > 0
        );
        invariant cur == x ==> (
            LC(C.k, C.next, C.prev,
                C.last, C.len, C.rlen, 
                C.keys, C.repr, cur)
            && C.last[cur] == x
        );
        invariant Unchanged(
            C.k, C.next, C.prev,
            C.last, C.len, C.rlen, 
            C.keys, C.repr, 
            C.k_pl1, C.next_pl1, C.prev_pl1,
            C.last_pl1, C.len_pl1, C.rlen_pl1, 
            C.keys_pl1, C.repr_pl1,
            x
        );
        invariant RefSetSubset(Br, EmptyRefSet[cur := true]);
        invariant Frame_all(
            C.k, C.next, C.prev,
            C.last, C.len, C.rlen, 
            C.keys, C.repr,
            old(C.k), old(C.next), old(C.prev),
            old(C.last), old(C.len), old(C.rlen), 
            old(C.keys), old(C.repr),
            old(C.repr)[old(C.last)[x]], 
            old(alloc)
        );
    {
        // Do we have a valid termination measure?
        call t := Get_len(cur);
        assert t >= 0;
        z := t;

        call IfNotBr_ThenLC(cur_next);
        call cur_prev := Get_prev(cur);
        call IfNotBr_ThenLC(cur_prev);
        call cur_prev_rlen := Get_rlen(cur_prev);
        call Set_rlen(cur, cur_prev_rlen + 1);
        call AssertLCAndRemove(cur);
        cur := cur_next;
        call cur_next := Get_next(cur);
        call IfNotBr_ThenLC(cur_next);

        // Has our termination measure decreased?
        call t := Get_len(cur);
        assert t < z;
    }
    call AssertLCAndRemove(cur);
}
