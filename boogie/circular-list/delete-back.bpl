// Supporting Artifact for
// "Predictive Verification using Intrinsic Definitions of Data Structures"
// by Adithya Murali, Cody Rivera, and P. Madhusudan.
// 
// Artifact by Cody Rivera, 2023. 
//
// Verification of Circular List Delete Back.

// Deletes at the back of a circular list (before the scaffolding node 'last').
//
// -> [x] -> [x.next] -> [x.next.next: last] ->
//         ==>
// -> [x] -> [x.next.next: last] ->

function {:inline} LC_Debug(
    k: [Ref]int, 
    next: [Ref]Ref,
    prev: [Ref]Ref,
    last: [Ref]Ref,
    len: [Ref]int,
    rlen: [Ref]int,
    keys: [Ref]KeySet,
    repr: [Ref]RefSet,
    x: Ref
) returns (bool)
{
    x != null ==> (
        next[prev[x]] == x
        && prev[next[x]] == x
        && (x == last[x] ==>
                len[x] == 0
                && rlen[x] == 0
                && last[x] == last[next[x]]
                && (next[x] == x ==>
                        KeySetsEqual(keys[x], EmptyKeySet)
                        && RefSetsEqual(repr[x], EmptyRefSet[x := true]))
                && (next[x] != x ==>
                        KeySetsEqual(keys[x], keys[next[x]])
                        && RefSetsEqual(repr[x], (repr[next[x]])[x := true])
                        && !(repr[next[x]])[x]))
        && (x != last[x] ==>
                len[x] == len[next[x]] + 1
                && rlen[x] == rlen[prev[x]] + 1
                && (next[x] == last[x] ==>
                        KeySetsEqual(keys[x], EmptyKeySet[k[x] := true])
                        && RefSetsEqual(repr[x], EmptyRefSet[x := true]))
                && (next[x] != last[x] ==>
                        KeySetsEqual(keys[x], (keys[next[x]])[k[x] := true])
                        && RefSetsEqual(repr[x], (repr[next[x]])[x := true])
                        && !(repr[next[x]])[x])
                && last[x] == last[next[x]]
                && last[last[x]] == last[x]
                && (repr[last[x]])[x]
                && (repr[last[x]])[prev[x]]
                && (repr[last[x]])[next[x]])
        && next[x] != null
        && prev[x] != null
        && last[x] != null
        && len[x] >= 0
        && rlen[x] >= 0
    )
}

procedure CircularDeleteBack(x: Ref, k: int)
    requires x != null;
    requires RefSetsEqual(Br, EmptyRefSet);
    requires LC(C.k, C.next, C.prev,
                C.last, C.len, C.rlen, 
                C.keys, C.repr, x);
    requires LC(C.k, C.next, C.prev,
                C.last, C.len, C.rlen, 
                C.keys, C.repr, C.next[x]);
    requires C.last[C.next[x]] == C.next[C.next[x]];
    requires C.next[x] != x;
    modifies Br, C.k, C.next, C.prev,
                C.last, C.len, C.rlen, 
                C.keys, C.repr;
    ensures LC(C.k, C.next, C.prev,
                C.last, C.len, C.rlen, 
                C.keys, C.repr, x);
    ensures C.next[x] == C.last[x];
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
    var last: Ref;

    // Subexpressions
    var x_last: Ref; var x_prev: Ref; var x_k: int;
    var cur_k: int; var cur_prev: Ref; var cur_next: Ref;
    var cur_next_keys: KeySet; var cur_next_repr: RefSet;
    var cur_next_len: int;

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
    call last := Get_next(next);
    call x_prev := Get_prev(x);
    call IfNotBr_ThenLC(x_prev);
    call IfNotBr_ThenLC(last);
    
    call Set_next(x, last);
    call Set_next(next, next);

    // repairing 'next'
    call Set_prev(next, next);
    call Set_len(next, 0);
    call Set_rlen(next, 0);
    call Set_keys(next, EmptyKeySet);
    call Set_repr(next, EmptyRefSet[next := true]);
    call Set_last(next, next);

    // repairing 'last'
    call Set_prev(last, x);
    call AssertLCAndRemove(next);

    if (x == last) {
        call DeleteFromLastRepr(x, next);
        call Set_keys(x, EmptyKeySet);
        call AssertLCAndRemove(x);
    } else {
        call x_k := Get_k(x);

        call Set_keys(x, EmptyKeySet[x_k := true]);
        call Set_repr(x, EmptyRefSet[x := true]);
        call Set_len(x, 1);
        call AssertLCAndRemove(x);

        // Save ghost loop state
        C.k_pl1 := C.k;
        C.next_pl1 := C.next;
        C.prev_pl1 := C.prev;
        C.last_pl1 := C.last;
        C.len_pl1 := C.len;
        C.rlen_pl1 := C.rlen;
        C.keys_pl1 := C.keys;
        C.repr_pl1 := C.repr;
        

        call cur := Get_prev(x);
        // while (cur != last)
        //     invariant cur != null;
        //     invariant last != null;
        //     invariant cur != last ==> (
        //         LC_Trans_PlusNode(C.k, C.next, C.prev,
        //             C.last, C.len, C.rlen, 
        //             C.keys, C.repr, cur, next)
        //         && LC(C.k, C.next, C.prev,
        //             C.last, C.len, C.rlen, 
        //             C.keys, C.repr, last)
        //         && cur != C.last[cur]
        //     );
        //     invariant cur == last ==> (
        //         LC_Trans_PlusNode(C.k, C.next, C.prev,
        //             C.last, C.len, C.rlen, 
        //             C.keys, C.repr, cur, next)
        //     );
        //     invariant (
        //         C.last[cur] == last
        //         && C.next[cur] != C.last[cur]
        //         && !(C.repr[C.next[cur]])[next]
        //     );
        //     invariant Unchanged(
        //         C.k, C.next, C.prev,
        //         C.last, C.len, C.rlen, 
        //         C.keys, C.repr, 
        //         C.k_pl1, C.next_pl1, C.prev_pl1,
        //         C.last_pl1, C.len_pl1, C.rlen_pl1, 
        //         C.keys_pl1, C.repr_pl1,
        //         x
        //     );
        //     invariant Unchanged(
        //         C.k, C.next, C.prev,
        //         C.last, C.len, C.rlen, 
        //         C.keys, C.repr, 
        //         C.k_pl1, C.next_pl1, C.prev_pl1,
        //         C.last_pl1, C.len_pl1, C.rlen_pl1, 
        //         C.keys_pl1, C.repr_pl1,
        //         last
        //     );
        //     invariant Unchanged(
        //         C.k, C.next, C.prev,
        //         C.last, C.len, C.rlen, 
        //         C.keys, C.repr, 
        //         C.k_pl1, C.next_pl1, C.prev_pl1,
        //         C.last_pl1, C.len_pl1, C.rlen_pl1, 
        //         C.keys_pl1, C.repr_pl1,
        //         next
        //     );
        //     invariant RefSetsEqual(Br, (EmptyRefSet[cur := true])[last := true]);
        // {
        //     // Do we have a valid termination measure?
        //     call t := Get_rlen(cur);
        //     assert t >= 0;
        //     z := t;

        //     call cur_prev := Get_prev(cur);
        //     call IfNotBr_ThenLC(cur_prev);
        //     call cur_k := Get_k(cur);
        //     call cur_next := Get_next(cur);
        //     call cur_next_keys := Get_keys(cur_next);
        //     call cur_next_repr := Get_repr(cur_next);
        //     call cur_next_len := Get_len(cur_next);
        //     call Set_keys(cur, cur_next_keys[cur_k := true]);
        //     call Set_repr(cur, cur_next_repr[cur := true]);
        //     call Set_len(cur, cur_next_len + 1);
        //     call AssertLCAndRemove(cur);

        //     cur := cur_prev;

        //     // Has our termination measure decreased?
        //     call t := Get_rlen(cur);
        //     assert t < z;
        // }

        havoc Br, C.k, C.next, C.prev,
                C.last, C.len, C.rlen, 
                C.keys, C.repr;

        havoc next, cur, last;

        assume cur != null;
        assume next != null;
        assume last != null;
        assume cur != last ==> (
            LC_Trans_PlusNode(C.k, C.next, C.prev,
                C.last, C.len, C.rlen, 
                C.keys, C.repr, cur, next)
            && LC(C.k, C.next, C.prev,
                C.last, C.len, C.rlen, 
                C.keys, C.repr, last)
            && cur != C.last[cur]
        );
        assume cur == last ==> (
            LC_Trans_PlusNode(C.k, C.next, C.prev,
                C.last, C.len, C.rlen, 
                C.keys, C.repr, cur, next)
        );
        assume (
            C.last[cur] == last
            && C.next[cur] != C.last[cur]
            && !(C.repr[C.next[cur]])[next]
            //&& (old(C.repr)[old(C.last)[x]])[cur]
            && (C.repr[last])[cur]
            && RefSetSubset(C.repr[last], old(C.repr)[old(C.last)[x]])
        );
        assume Unchanged(
            C.k, C.next, C.prev,
            C.last, C.len, C.rlen, 
            C.keys, C.repr, 
            C.k_pl1, C.next_pl1, C.prev_pl1,
            C.last_pl1, C.len_pl1, C.rlen_pl1, 
            C.keys_pl1, C.repr_pl1,
            x
        );
        assume Unchanged(
            C.k, C.next, C.prev,
            C.last, C.len, C.rlen, 
            C.keys, C.repr, 
            C.k_pl1, C.next_pl1, C.prev_pl1,
            C.last_pl1, C.len_pl1, C.rlen_pl1, 
            C.keys_pl1, C.repr_pl1,
            last
        );
        assume Unchanged(
            C.k, C.next, C.prev,
            C.last, C.len, C.rlen, 
            C.keys, C.repr, 
            C.k_pl1, C.next_pl1, C.prev_pl1,
            C.last_pl1, C.len_pl1, C.rlen_pl1, 
            C.keys_pl1, C.repr_pl1,
            next
        );
        assume C.next[next] == next && C.prev[next] == next;
        assume RefSetsEqual(Br, (EmptyRefSet[cur := true])[last := true]);
        assume Frame_all(
            C.k, C.next, C.prev,
            C.last, C.len, C.rlen, 
            C.keys, C.repr,
            old(C.k), old(C.next), old(C.prev),
            old(C.last), old(C.len), old(C.rlen), 
            old(C.keys), old(C.repr),
            old(C.repr)[old(C.last)[x]], 
            old(alloc)
        );
        assume cur != last;

        // Do we have a valid termination measure?
            call t := Get_rlen(cur);
            assert t >= 0;
            z := t;

            call cur_prev := Get_prev(cur);
            call IfNotBr_ThenLC(cur_prev);
            call cur_k := Get_k(cur);
            call cur_next := Get_next(cur);
            call IfNotBr_ThenLC(cur_next);
            call cur_next_keys := Get_keys(cur_next);
            call cur_next_repr := Get_repr(cur_next);
            call cur_next_len := Get_len(cur_next);
            call Set_keys(cur, cur_next_keys[cur_k := true]);
            call Set_repr(cur, cur_next_repr[cur := true]);
            call Set_len(cur, cur_next_len + 1);
            assert LC_Debug(C.k, C.next, C.prev,
                C.last, C.len, C.rlen, 
                C.keys, C.repr, cur);
            call AssertLCAndRemove(cur);

            cur := cur_prev;

            // Has our termination measure decreased?
            call t := Get_rlen(cur);
            assert t < z;

        assert cur != null;
        assert next != null;
        assert last != null;
        assert cur != last ==> (
            LC_Trans_PlusNode(C.k, C.next, C.prev,
                C.last, C.len, C.rlen, 
                C.keys, C.repr, cur, next)
            && LC(C.k, C.next, C.prev,
                C.last, C.len, C.rlen, 
                C.keys, C.repr, last)
            && cur != C.last[cur]
        );
        assert cur == last ==> (
            LC_Trans_PlusNode(C.k, C.next, C.prev,
                C.last, C.len, C.rlen, 
                C.keys, C.repr, cur, next)
        );
        assert (
            C.last[cur] == last
            && C.next[cur] != C.last[cur]
            && !(C.repr[C.next[cur]])[next]
            //&& (old(C.repr)[old(C.last)[x]])[cur]
            && (C.repr[last])[cur]
            && RefSetSubset(C.repr[last], old(C.repr)[old(C.last)[x]])
        );
        assert Unchanged(
            C.k, C.next, C.prev,
            C.last, C.len, C.rlen, 
            C.keys, C.repr, 
            C.k_pl1, C.next_pl1, C.prev_pl1,
            C.last_pl1, C.len_pl1, C.rlen_pl1, 
            C.keys_pl1, C.repr_pl1,
            x
        );
        assert Unchanged(
            C.k, C.next, C.prev,
            C.last, C.len, C.rlen, 
            C.keys, C.repr, 
            C.k_pl1, C.next_pl1, C.prev_pl1,
            C.last_pl1, C.len_pl1, C.rlen_pl1, 
            C.keys_pl1, C.repr_pl1,
            last
        );
        assert Unchanged(
            C.k, C.next, C.prev,
            C.last, C.len, C.rlen, 
            C.keys, C.repr, 
            C.k_pl1, C.next_pl1, C.prev_pl1,
            C.last_pl1, C.len_pl1, C.rlen_pl1, 
            C.keys_pl1, C.repr_pl1,
            next
        );
        assert C.next[next] == next && C.prev[next] == next;
        assert RefSetsEqual(Br, (EmptyRefSet[cur := true])[last := true]);
        assert Frame_all(
            C.k, C.next, C.prev,
            C.last, C.len, C.rlen, 
            C.keys, C.repr,
            old(C.k), old(C.next), old(C.prev),
            old(C.last), old(C.len), old(C.rlen), 
            old(C.keys), old(C.repr),
            old(C.repr)[old(C.last)[x]], 
            old(alloc)
        );


        assume false;
    }

    // // Save ghost loop state
    // C.k_pl1 := C.k;
    // C.next_pl1 := C.next;
    // C.prev_pl1 := C.prev;
    // C.last_pl1 := C.last;
    // C.len_pl1 := C.len;
    // C.rlen_pl1 := C.rlen;
    // C.keys_pl1 := C.keys;
    // C.repr_pl1 := C.repr;
    
    // call cur := Get_next(x);
    // call cur_next := Get_next(cur);
    // call IfNotBr_ThenLC(cur_next);
    // while (cur != x)
    //     invariant cur != null;
    //     invariant cur_next == C.next[cur];
    //     invariant cur != x ==> (
    //         RefSetsEqual(Br, EmptyRefSet[cur := true])
    //         && LC_Trans_NoRlen(C.k, C.next, C.prev,
    //             C.last, C.len, C.rlen, 
    //             C.keys, C.repr, cur)
    //         && C.last[cur] == x
    //         && C.len[cur] > 0
    //     );
    //     invariant cur == x ==> (
    //         LC(C.k, C.next, C.prev,
    //             C.last, C.len, C.rlen, 
    //             C.keys, C.repr, cur)
    //         && C.last[cur] == x
    //     );
    //     invariant Unchanged(
    //         C.k, C.next, C.prev,
    //         C.last, C.len, C.rlen, 
    //         C.keys, C.repr, 
    //         C.k_pl1, C.next_pl1, C.prev_pl1,
    //         C.last_pl1, C.len_pl1, C.rlen_pl1, 
    //         C.keys_pl1, C.repr_pl1,
    //         x
    //     );
    //     invariant RefSetSubset(Br, EmptyRefSet[cur := true]);
    //     invariant Frame_all(
    //         C.k, C.next, C.prev,
    //         C.last, C.len, C.rlen, 
    //         C.keys, C.repr,
    //         old(C.k), old(C.next), old(C.prev),
    //         old(C.last), old(C.len), old(C.rlen), 
    //         old(C.keys), old(C.repr),
    //         old(C.repr)[old(C.last)[x]], 
    //         old(alloc)
    //     );
    // {
    //     // Do we have a valid termination measure?
    //     call t := Get_len(cur);
    //     assert t >= 0;
    //     z := t;

    //     call IfNotBr_ThenLC(cur_next);
    //     call cur_prev := Get_prev(cur);
    //     call IfNotBr_ThenLC(cur_prev);
    //     call cur_prev_rlen := Get_rlen(cur_prev);
    //     call Set_rlen(cur, cur_prev_rlen + 1);
    //     call AssertLCAndRemove(cur);
    //     cur := cur_next;
    //     call cur_next := Get_next(cur);
    //     call IfNotBr_ThenLC(cur_next);

    //     // Has our termination measure decreased?
    //     call t := Get_len(cur);
    //     assert t < z;
    // }
    // call AssertLCAndRemove(cur);
}
