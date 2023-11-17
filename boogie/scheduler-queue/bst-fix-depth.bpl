// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions of Data Structures"
// by Anonymous Authors.
// 
// Artifact by Anonymous Author, 2023. 
//
// Verification of depth fixing for BSTs, for overlaid Data Structures.
//
// Since this is a ghost method, we must explicitly prove termination in
// order for the framework to be sound.

procedure BSTFixDepthContract(q1s: Ref, q1t: Ref, x: Ref);
    requires x != null;
    requires RefSetsDisjoint(
        (C.bst_repr[x])[x := false],
        Br_bst
    );
    requires RefSetsEqual(Br_list, EmptyRefSet);
    requires LC_Trans_NoDepth(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, x);
    requires C.p[x] != null;
    modifies Br_bst, Br_list, C.bst_depth;
    ensures LC(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, x);
    ensures RefSetsEqual(Br_bst, old(Br_bst)[x := false]);
    ensures RefSetsEqual(Br_list, EmptyRefSet);
    // Framing conditions
    ensures Frame_all(
        C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
        C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
        C.next, C.prev, C.list_keys, C.list_repr,
        old(C.k), old(C.l), old(C.r), old(C.p), old(C.min), old(C.max), old(C.bst_size),
        old(C.bst_keys), old(C.bst_repr), old(C.bst_depth), old(C.bst_root),
        old(C.next), old(C.prev), old(C.list_keys), old(C.list_repr),
        RefSetIntersectF(old(C.bst_repr)[x], old(C.bst_repr)[old(C.bst_root)[x]]), old(alloc)
    );

procedure BSTFixDepth(q1s: Ref, q1t: Ref, x: Ref)
    requires x != null;
    requires RefSetsDisjoint(
        (C.bst_repr[x])[x := false],
        Br_bst
    );
    requires RefSetsEqual(Br_list, EmptyRefSet);
    requires LC_Trans_NoDepth(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, x);
    requires C.p[x] != null;
    modifies Br_bst, Br_list, C.bst_depth;
    ensures LC(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, x);
    ensures RefSetsEqual(Br_bst, old(Br_bst)[x := false]);
    ensures RefSetsEqual(Br_list, EmptyRefSet);
    // Framing conditions
    ensures Frame_all(
        C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
        C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
        C.next, C.prev, C.list_keys, C.list_repr,
        old(C.k), old(C.l), old(C.r), old(C.p), old(C.min), old(C.max), old(C.bst_size),
        old(C.bst_keys), old(C.bst_repr), old(C.bst_depth), old(C.bst_root),
        old(C.next), old(C.prev), old(C.list_keys), old(C.list_repr),
        RefSetIntersectF(old(C.bst_repr)[x], old(C.bst_repr)[old(C.bst_root)[x]]), old(alloc)
    );
{
    // Subexpressions
    var x_l: Ref;
    var x_r: Ref;
    var x_p: Ref;
    var x_p_bst_depth: int;
    var x_l_bst_size: int;
    var x_r_bst_size: int;

    // Termination measure variables.
    var t: int;
    var z: int;

    // Do we have a valid termination measure?
    call t := Get_bst_size(x);
    assert t >= 0;
    // Store termination measure.
    z := t;

    call InAllocParam(q1s);
    call InAllocParam(q1t);
    call InAllocParam(x);

    call x_l := Get_l(x);
    call x_r := Get_r(x);
    if (x_l != null) {
        call IfNotBr_ThenLC(x_l);
    }
    if (x_r != null) {
        call IfNotBr_ThenLC(x_r);
    }
    call x_p := Get_p(x);
    call x_p_bst_depth := Get_bst_depth(x_p);
    call Set_bst_depth(x, 1 + x_p_bst_depth);
    call AssertLCAndRemove(x);

    call x_l := Get_l(x);
    call x_r := Get_r(x);
    if (x_l != null) {
        call x_l_bst_size := Get_bst_size(x_l);
        t := x_l_bst_size;
        // Does our measure decrease before our call?
        assert t < z;
        call BSTFixDepthContract(q1s, q1t, x_l);
    }
    if (x_r != null) {
        call IfNotBrList_ThenListLC(x_r);
        call x_r_bst_size := Get_bst_size(x_r);
        t := x_r_bst_size;
        // Does our measure decrease before our call?
        assert t < z;
        call BSTFixDepthContract(q1s, q1t, x_r);
    }
    call IfNotBrList_ThenListLC(x);
}
