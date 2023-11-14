// Supporting Artifact for
// "Predictive Verification using Intrinsic Definitions of Data Structures"
// by Adithya Murali, Cody Rivera, and P. Madhusudan.
// 
// Artifact by Cody Rivera, 2023. 
//
// Verification of Circular List Insert Back.

// Insert at the back of a circular list (before the scaffolding node 'last').
// 
// -> [x] -> [x.next: last] ->
//          ==>
// -> [x] -> [new node] -> [x.next: last] ->
// (return value 'ret' is the new node)

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
                //&& rlen[x] == rlen[prev[x]] + 1
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
                && (repr[last[x]])[next[x]]
                )
        && next[x] != null
        && prev[x] != null
        && last[x] != null
        && len[x] >= 0
        //&& rlen[x] >= 0
    )
}

procedure CircularInsertBack(x: Ref, k: int) returns (ret: Ref)
    requires x != null;
    requires RefSetsEqual(Br, EmptyRefSet);
    requires LC(C.k, C.next, C.prev,
                C.last, C.len, C.rlen, 
                C.keys, C.repr, x);
    requires C.last[x] == C.next[x];
    modifies Br, alloc, C.k, C.next, C.prev,
                C.last, C.len, C.rlen, 
                C.keys, C.repr;
    ensures RefSetSubset(old(alloc), alloc);
    ensures ret != null;
    ensures LC(C.k, C.next, C.prev,
                C.last, C.len, C.rlen, 
                C.keys, C.repr, ret);
    ensures C.next[ret] == C.last[ret];
    ensures C.last[ret] == old(C.last)[x];
    ensures KeySetsEqual(C.keys[C.last[ret]], (old(C.keys)[old(C.last)[x]])[k := true]);
    ensures Fresh(RefSetDiffF(C.repr[C.last[ret]], old(C.repr)[old(C.last)[x]]), alloc, old(alloc));
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
    var last: Ref;
    var node: Ref;
    var cur: Ref;

    // Subexpressions
    var x_last: Ref; var x_prev: Ref; var x_next: Ref;
    var node_prev: Ref; var node_prev_rlen: int;
    var node_prev_last: Ref;
    var cur_prev: Ref; var cur_next: Ref; var cur_next_len: int;
    var cur_repr: RefSet; var cur_keys: KeySet; var node_k: int;
    var cur_next_keys: KeySet;
    

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

    call x_prev := Get_prev(x);
    call x_next := Get_next(x);
    call IfNotBr_ThenLC(x_prev);
    call IfNotBr_ThenLC(x_next);
    
    last := x_next;

    call node := Create(k);
    call Set_next(node, x_next);
    call Set_next(x, node);

    // Updating ghost fields of last
    call AddToLastRepr(last, node);
    call Set_prev(last, node);

    // Repairing 'node'
    call Set_prev(node, x);
    call Set_len(node, 1);
    call node_prev := Get_prev(node);
    call node_prev_rlen := Get_rlen(node_prev);
    call Set_rlen(node, 1 + node_prev_rlen);
    call Set_keys(node, EmptyKeySet[k := true]);
    call Set_repr(node, EmptyRefSet[node := true]);
    call node_prev_last := Get_last(node_prev);
    call Set_last(node, node_prev_last);
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

    cur := x;
    while (cur != last) 
        invariant cur != null;
        invariant cur != last ==> (
            RefSetsEqual(Br, EmptyRefSet[cur := true][last := true])
            && LC_Trans_MinusNode(C.k, C.next, C.prev,
                C.last, C.len, C.rlen, 
                C.keys, C.repr, cur, node)
            && C.last[cur] == last
            && LC_At_Last(C.k, C.next, C.prev,
                C.last, C.len, C.rlen, 
                C.keys, C.repr, last, node)
        );
        invariant cur == last ==> (
            LC_Trans_MinusNode(C.k, C.next, C.prev,
                C.last, C.len, C.rlen, 
                C.keys, C.repr, cur, node)
        );
        invariant (C.repr[C.next[cur]])[node];
        invariant (C.keys[C.next[cur]])[C.k[node]];
        invariant Unchanged(
            C.k, C.next, C.prev,
            C.last, C.len, C.rlen, 
            C.keys, C.repr, 
            C.k_pl1, C.next_pl1, C.prev_pl1,
            C.last_pl1, C.len_pl1, C.rlen_pl1, 
            C.keys_pl1, C.repr_pl1,
            node
        );
        invariant Unchanged(
            C.k, C.next, C.prev,
            C.last, C.len, C.rlen, 
            C.keys, C.repr, 
            C.k_pl1, C.next_pl1, C.prev_pl1,
            C.last_pl1, C.len_pl1, C.rlen_pl1, 
            C.keys_pl1, C.repr_pl1,
            last
        );
        invariant RefSetSubset(Br, EmptyRefSet[cur := true][last := true]);
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
        call t := Get_rlen(cur);
        assert t >= 0;
        z := t;

        call cur_prev := Get_prev(cur);
        call cur_next := Get_next(cur);
        call IfNotBr_ThenLC(cur_prev);
        call IfNotBr_ThenLC(cur_next);
        call cur_next_len := Get_len(cur_next);
        call Set_len(cur, cur_next_len + 1);
        call cur_repr := Get_repr(cur);
        call Set_repr(cur, cur_repr[node := true]);
        call cur_keys := Get_keys(cur);
        call node_k := Get_k(node);
        call Set_keys(cur, cur_keys[node_k := true]);
        call AssertLCAndRemove(cur);
        cur := cur_prev;

        // Has our termination measure decreased?
        call t := Get_rlen(cur);
        assert t < z;
    }
    call IfNotBr_ThenLC(node);
    call cur_next := Get_next(cur);
    call cur_next_keys := Get_keys(cur_next);
    call Set_keys(cur, cur_next_keys);
    call AssertLCAndRemove(cur);
    call AssertLCAndRemove(node);

    ret := node;
}