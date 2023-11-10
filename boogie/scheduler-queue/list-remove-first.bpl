// Supporting Artifact for
// "Predictive Verification using Intrinsic Definitions of Data Structures"
// by Adithya Murali, Cody Rivera, and P. Madhusudan.
// 
// Artifact by Cody Rivera, 2023. 
//
// Verification of removing the first item from a list, for the scheduler
// queue (overlay of List and BST).

procedure ListRemoveFirst(q1s: Ref, q1t: Ref, x: Ref)
    returns (ret: Ref, node: Ref)
    requires RefSetsEqual(Br_bst, EmptyRefSet);
    requires RefSetsEqual(Br_list, EmptyRefSet);
    requires x != null ==> 
        LC(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
            C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
            C.next, C.prev, C.list_keys, C.list_repr, x);
    requires x != null ==> C.prev[x] == null;
    modifies Br_bst, Br_list, C.next, C.prev, C.list_keys, C.list_repr;
    ensures x == null ==> ret == null;
    ensures x != null ==> ret == old(C.next)[x];
    ensures node == x;
    ensures (ret != null ==>
                LC(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                    C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                    C.next, C.prev, C.list_keys, C.list_repr, x)
                && C.prev[ret] == null
                && RefSetsEqual(C.list_repr[ret], (old(C.list_repr)[x])[node := false])
                && KeySetsEqual(C.list_keys[ret], (old(C.list_keys)[x])[C.k[node] := false]));
    ensures (node != null ==>
                LC(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                    C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                    C.next, C.prev, C.list_keys, C.list_repr, x)
                && C.k[node] == old(C.k)[x]
                && C.next[node] == null
                && C.prev[node] == null);
    ensures RefSetsEqual(Br_bst, EmptyRefSet);
    ensures RefSetsEqual(Br_list, EmptyRefSet);
    // Framing conditions
    ensures Frame_all(
        C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
        C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
        C.next, C.prev, C.list_keys, C.list_repr,
        old(C.k), old(C.l), old(C.r), old(C.p), old(C.min), old(C.max), old(C.bst_size),
        old(C.bst_keys), old(C.bst_repr), old(C.bst_depth), old(C.bst_root),
        old(C.next), old(C.prev), old(C.list_keys), old(C.list_repr),
        if x == null then EmptyRefSet else old(C.list_repr)[x],
        old(alloc)
    );
{
    // Subexpressions
    var x_next: Ref;
    var node_k: int;

    call InAllocParam(q1s);
    call InAllocParam(q1t);
    call InAllocParam(x);

    if (x == null) {
        ret := null;
        node := null;
        return;
    }
    
    call x_next := Get_next(x);
    call IfNotBr_ThenLC(x_next);

    node := x;
    ret := x_next;
    call Set_prev(node, null);
    call Set_next(node, null);
    call node_k := Get_k(node);
    call Set_list_keys(node, EmptyKeySet[node_k := true]);
    call Set_list_repr(node, EmptyRefSet[node := true]);
    if (ret != null) {
        call Set_prev(ret, null);
    }
    call AssertLCAndRemove(node);
    call AssertLCAndRemove(ret);
}