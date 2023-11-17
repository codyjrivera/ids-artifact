// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions of Data Structures"
// by Anonymous Authors.
// 
// Artifact by Anonymous Author, 2023. 
//
// Verification of Circular List Insert Front.

// Insert at the front of a circular list.
// 
// -> [x: last] -> [x.next] ->
//          ==>
// -> [x: last] -> [new node] -> [x.next] ->

procedure CircularInsertFront(x: Ref, k: int)
    requires x != null;
    requires RefSetsEqual(Br, EmptyRefSet);
    requires LC(C.k, C.next, C.prev,
                C.last, C.len, C.rlen, 
                C.keys, C.repr, x);
    requires C.last[x] == x;
    modifies Br, alloc, C.k, C.next, C.prev,
                C.last, C.len, C.rlen, 
                C.keys, C.repr;
    ensures RefSetSubset(old(alloc), alloc);
    ensures LC(C.k, C.next, C.prev,
                C.last, C.len, C.rlen, 
                C.keys, C.repr, x);
    ensures C.last[x] == x;
    ensures KeySetsEqual(C.keys[C.last[x]], (old(C.keys)[old(C.last)[x]])[k := true]);
    ensures Fresh(RefSetDiffF(C.repr[C.last[x]], old(C.repr)[old(C.last)[x]]), alloc, old(alloc));
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
    var node: Ref;
    var cur: Ref;

    // Subexpressions
    var x_last: Ref;
    var x_next: Ref; var x_prev: Ref;
    var x_next_next: Ref;
    var node_next: Ref;
    var node_next_len: int;
    var node_next_keys: KeySet;
    var node_next_repr: RefSet;
    var cur_next: Ref;
    var cur_prev: Ref;
    var cur_prev_rlen: int;

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

    call x_next := Get_next(x);
    call IfNotBr_ThenLC(x_next);
    call x_next_next := Get_next(x);
    call IfNotBr_ThenLC(x_next_next);

    call node := Create(k);
    call Set_next(node, x_next);
    call Set_next(x, node);

    // repairing 'node'
    call Set_last(node, x);
    call Set_rlen(node, 1);
    call node_next := Get_next(node);
    call node_next_len := Get_len(node_next);
    call Set_len(node, node_next_len + 1);
    call node_next_keys := Get_keys(node_next);
    call node_next_repr := Get_repr(node_next);
    call Set_keys(node, (if node_next == x then EmptyKeySet else node_next_keys)[k := true]);
    call Set_repr(node, (if node_next == x then EmptyRefSet else node_next_repr)[node := true]);
    call Set_prev(node_next, node);

    // repairing 'x'
    call x_prev := Get_prev(x);
    if (x_prev == x) {
        call Set_prev(x, node);
    }
    call Set_prev(node, x);
    call AddToLastRepr(x, node);
    call AddToLastKeys(x, k);

    call AssertLCAndRemove(x);
    call AssertLCAndRemove(node);

    // Save ghost loop state
    C.k_pl1 := C.k;
    C.next_pl1 := C.next;
    C.prev_pl1 := C.prev;
    C.last_pl1 := C.last;
    C.len_pl1 := C.len;
    C.rlen_pl1 := C.rlen;
    C.keys_pl1 := C.keys;
    C.repr_pl1 := C.repr;
    
    call cur := Get_next(node);
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