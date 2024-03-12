// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions"
// by Anonymous Authors.
// 
// Artifact by Anonymous Author, 2023. 
//
// Verification of depth fixing for BSTs with scaffolding nodes.
//
// Since this is a ghost method, we must explicitly prove termination in
// order for the framework to be sound.

procedure BSTFixDepthContract(x: Ref);
    requires x != null;
    requires RefSetsDisjoint(
        (C.repr[x])[x := false],
        Br
    );
    requires LC_Trans_NoDepth(C.k, C.l, C.r, C.p, C.min, C.max, C.size,
                C.keys, C.repr, C.depth, C.root, x);
    requires C.p[x] != null;
    modifies Br, C.depth;
    ensures LC(C.k, C.l, C.r, C.p, C.min, C.max, C.size,
                C.keys, C.repr, C.depth, C.root, x);
    ensures RefSetsEqual(Br, old(Br)[x := false]);
    // Framing conditions
    ensures Frame_all(
        C.k, C.l, C.r, C.p, C.min, C.max, C.size,
        C.keys, C.repr, C.depth, C.root,
        old(C.k), old(C.l), old(C.r), old(C.p), old(C.min), old(C.max), old(C.size),
        old(C.keys), old(C.repr), old(C.depth), old(C.root),
        RefSetIntersectF(old(C.repr)[x], old(C.repr)[old(C.root)[x]]), old(alloc)
    );

procedure BSTFixDepth(x: Ref)
    requires x != null;
    requires RefSetsDisjoint(
        (C.repr[x])[x := false],
        Br
    );
    requires LC_Trans_NoDepth(C.k, C.l, C.r, C.p, C.min, C.max, C.size,
                C.keys, C.repr, C.depth, C.root, x);
    requires C.p[x] != null;
    modifies Br, C.depth;
    ensures LC(C.k, C.l, C.r, C.p, C.min, C.max, C.size,
                C.keys, C.repr, C.depth, C.root, x);
    ensures RefSetsEqual(Br, old(Br)[x := false]);
    // Framing conditions
    ensures Frame_all(
        C.k, C.l, C.r, C.p, C.min, C.max, C.size,
        C.keys, C.repr, C.depth, C.root,
        old(C.k), old(C.l), old(C.r), old(C.p), old(C.min), old(C.max), old(C.size),
        old(C.keys), old(C.repr), old(C.depth), old(C.root),
        RefSetIntersectF(old(C.repr)[x], old(C.repr)[old(C.root)[x]]), old(alloc)
    );
{
    // Subexpressions
    var x_l: Ref;
    var x_r: Ref;
    var x_p: Ref;
    var x_p_depth: int;
    var x_l_size: int;
    var x_r_size: int;

    // Termination measure variables.
    var t: int;
    var z: int;

    // Do we have a valid termination measure?
    call t := Get_size(x);
    assert t >= 0;
    // Store termination measure.
    z := t;

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
    call x_p_depth := Get_depth(x_p);
    call Set_depth(x, 1 + x_p_depth);
    call AssertLCAndRemove(x);

    call x_l := Get_l(x);
    call x_r := Get_r(x);
    if (x_l != null) {
        call x_l_size := Get_size(x_l);
        t := x_l_size;
        // Does our measure decrease before our call?
        assert t < z;
        call BSTFixDepthContract(x_l);
    }
    if (x_r != null) {
        call x_r_size := Get_size(x_r);
        t := x_r_size;
        // Does our measure decrease before our call?
        assert t < z;
        call BSTFixDepthContract(x_r);
    }
}
