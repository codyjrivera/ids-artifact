// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions"
// by Anonymous Authors.
// 
// Artifact by Anonymous Author, 2023. 
//
// Verification of deleting inside a BST, for BSTs with scaffolding.

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

procedure BSTRemoveRootInsideContract(x: Ref)
    returns (ret: Ref, root: Ref);
    requires x != null;
    requires RefSetsDisjoint(
        C.repr[x],
        Br
    );
    requires LC(C.k, C.l, C.r, C.p, C.min, C.max, C.size,
                C.keys, C.repr, C.depth, C.root, x);
    requires C.p[x] != null;
    requires C.l[C.p[x]] == x || C.r[C.p[x]] == x;
    requires !(C.l[C.p[x]] == x && C.r[C.p[x]] == x);
    modifies Br, C.l, C.r, C.p, C.min, C.max, C.size,
                C.keys, C.repr, C.depth, C.root;
    ensures root != null;
    ensures ret == null || ret == old(C.l)[x] || ret == old(C.r)[x];
    ensures (RefSetsEqual(old(C.repr)[x], EmptyRefSet[x := true]) ==> ret == null);
    ensures ((RefSetSubset(EmptyRefSet[x := true], old(C.repr)[x]) 
             && !RefSetsEqual(old(C.repr)[x], EmptyRefSet[x := true]))
                ==> ret != null);
    ensures (ret != null ==>
                LC(C.k, C.l, C.r, C.p, C.min, C.max, C.size,
                    C.keys, C.repr, C.depth, C.root, ret)
                && KeySetsEqual(C.keys[ret], (old(C.keys)[x])[C.k[x] := false])
                && C.min[ret] >= old(C.min)[x]
                && C.max[ret] <= old(C.max)[x]
                && RefSetsEqual(C.repr[ret], (old(C.repr)[x])[x := false])
                && C.root[ret] == old(C.root)[x]
                && C.p[ret] == old(C.p)[x]);
    ensures old(C.l)[old(C.p)[x]] == x ==> C.l[old(C.p)[x]] == ret;
    ensures old(C.l)[old(C.p)[x]] != x ==> C.l[old(C.p)[x]] == old(C.l)[old(C.p)[x]];
    ensures old(C.r)[old(C.p)[x]] == x ==> C.r[old(C.p)[x]] == ret;
    ensures old(C.r)[old(C.p)[x]] != x ==> C.r[old(C.p)[x]] == old(C.r)[old(C.p)[x]];
    ensures old(C.k)[old(C.p)[x]] == C.k[old(C.p)[x]];
    ensures old(C.p)[old(C.p)[x]] == C.p[old(C.p)[x]];
    ensures old(C.size)[old(C.p)[x]] == C.size[old(C.p)[x]];
    ensures KeySetsEqual(old(C.keys)[old(C.p)[x]], C.keys[old(C.p)[x]]);
    ensures RefSetsEqual(old(C.repr)[old(C.p)[x]], C.repr[old(C.p)[x]]);
    ensures old(C.min)[old(C.p)[x]] == C.min[old(C.p)[x]];
    ensures old(C.max)[old(C.p)[x]] == C.max[old(C.p)[x]];
    ensures old(C.depth)[old(C.p)[x]] == C.depth[old(C.p)[x]];
    ensures old(C.root)[old(C.p)[x]] == C.root[old(C.p)[x]];
    ensures root == x && C.k[root] == old(C.k)[x];
    ensures LC(C.k, C.l, C.r, C.p, C.min, C.max, C.size,
                C.keys, C.repr, C.depth, C.root, root);
    ensures Isolated(C.k, C.l, C.r, C.p, C.min, C.max, C.size,
                C.keys, C.repr, C.depth, C.root, root);
    ensures old(C.p)[x] == null ==> RefSetsEqual(Br, old(Br));
    ensures old(C.p)[x] != null ==> RefSetsEqual(Br, old(Br)[old(C.p)[x] := true]);
    // Framing conditions
    ensures Frame_all(
        C.k, C.l, C.r, C.p, C.min, C.max, C.size,
        C.keys, C.repr, C.depth, C.root,
        old(C.k), old(C.l), old(C.r), old(C.p), old(C.min), old(C.max), old(C.size),
        old(C.keys), old(C.repr), old(C.depth), old(C.root),
        RefSetIntersectF(old(C.repr)[x], old(C.repr)[old(C.root)[x]])[old(C.p)[x] := true],
        old(alloc)
    );

procedure BSTDeleteInside(root: Ref, x: Ref)
    returns (ret: Ref, node: Ref)
    requires root != null && x != null;
    requires RefSetsEqual(Br, EmptyRefSet);
    requires LC(C.k, C.l, C.r, C.p, C.min, C.max, C.size,
                C.keys, C.repr, C.depth, C.root, x);
    requires C.p[x] != null;
    requires C.l[C.p[x]] == x || C.r[C.p[x]] == x;
    requires !(C.l[C.p[x]] == x && C.r[C.p[x]] == x);
    requires C.root[x] == root;
    modifies Br, C.l, C.r, C.p, C.min, C.max, C.size,
                C.keys, C.repr, C.depth, C.root;
    ensures node != null;
    ensures ret == null || ret == old(C.l)[x] || ret == old(C.r)[x];
    ensures (RefSetsEqual(old(C.repr)[x], EmptyRefSet[x := true]) ==> ret == null);
    ensures ((RefSetSubset(EmptyRefSet[x := true], old(C.repr)[x]) 
             && !RefSetsEqual(old(C.repr)[x], EmptyRefSet[x := true]))
                ==> ret != null);
    ensures (ret != null ==>
                LC(C.k, C.l, C.r, C.p, C.min, C.max, C.size,
                    C.keys, C.repr, C.depth, C.root, ret)
                && KeySetsEqual(C.keys[ret], (old(C.keys)[x])[C.k[x] := false])
                && C.min[ret] >= old(C.min)[x]
                && C.max[ret] <= old(C.max)[x]
                && RefSetsEqual(C.repr[ret], (old(C.repr)[x])[x := false])
                && C.root[ret] == root
                && C.p[ret] == old(C.p)[x]);
    ensures KeySetsEqual(C.keys[root], (old(C.keys)[root])[C.k[x] := false]);
    ensures C.min[root] == old(C.min)[root];
    ensures C.max[root] == old(C.max)[root];
    ensures RefSetsEqual(C.repr[root], (old(C.repr)[root])[x := false]);
    ensures C.root[root] == old(C.root)[root];
    ensures C.p[root] == old(C.p)[root];
    ensures node == x && C.k[node] == old(C.k)[x];
    ensures LC(C.k, C.l, C.r, C.p, C.min, C.max, C.size,
                C.keys, C.repr, C.depth, C.root, node);
    ensures Isolated(C.k, C.l, C.r, C.p, C.min, C.max, C.size,
                C.keys, C.repr, C.depth, C.root, node);
    ensures RefSetsEqual(Br, EmptyRefSet);
    // Framing conditions
    ensures Frame_all(
        C.k, C.l, C.r, C.p, C.min, C.max, C.size,
        C.keys, C.repr, C.depth, C.root,
        old(C.k), old(C.l), old(C.r), old(C.p), old(C.min), old(C.max), old(C.size),
        old(C.keys), old(C.repr), old(C.depth), old(C.root),
        old(C.repr)[old(C.root)[x]],
        old(alloc)
    );
{
    // Local variables
    var p: Ref;
    var cur: Ref;

    // Subexpressions
    var p_l: Ref; var p_r: Ref; var cur_p: Ref;
    var cur_l: Ref; var cur_r: Ref; var cur_k: int;
    var cur_l_size: int; var cur_r_size: int;
    var cur_l_min: int; var cur_l_keys: KeySet;
    var cur_l_repr: RefSet;
    var cur_r_max: int; var cur_r_keys: KeySet;
    var cur_r_repr: RefSet;

    // Heap value, PreLoop0:
    var C.k_pl0: [Ref]int;
    var C.l_pl0: [Ref]Ref; var C.r_pl0: [Ref]Ref;
    var C.p_pl0: [Ref]Ref; var C.min_pl0: [Ref]int; var C.max_pl0: [Ref]int;
    var C.size_pl0: [Ref]int; var C.keys_pl0: [Ref]KeySet; var C.repr_pl0: [Ref]RefSet;
    var C.depth_pl0: [Ref]int; var C.root_pl0: [Ref]Ref;

    // Loop termination
    var t: int;
    var z: int;

    call InAllocParam(root);
    call InAllocParam(x);

    call p := Get_p(x);
    call IfNotBr_ThenLC(p);
    call p_l := Get_l(p);
    call p_r := Get_r(p);
    if (p_l != null) {
        call IfNotBr_ThenLC(p_l);
    }
    if (p_r != null) {
        call IfNotBr_ThenLC(p_r);
    }
    call ret, node := BSTRemoveRootInsideContract(x);
    cur := p;

    // label PreLoop0:
    C.k_pl0 := C.k;
    C.l_pl0 := C.l; C.r_pl0 := C.r;
    C.p_pl0 := C.p; C.min_pl0 := C.min; C.max_pl0 := C.max;
    C.size_pl0 := C.size; C.keys_pl0 := C.keys; C.repr_pl0 := C.repr;
    C.depth_pl0 := C.depth; C.root_pl0 := C.root;

    // Since this is a ghost loop, we must prove termination of it
    call cur_p := Get_p(cur);

    while (cur_p != null)
        invariant cur != null;
        invariant cur_p == C.p[cur];
        invariant RefSetsEqual(Br, EmptyRefSet[cur := true]);
        invariant LC_Trans_PlusNode(C.k, C.l, C.r, C.p, C.min, C.max, C.size,
                C.keys, C.repr, C.depth, C.root, cur, node);
        invariant (C.keys[cur])[C.k[node]];
        invariant C.p[cur] != null && C.l[cur] != null ==> (
            !(C.repr[C.l[cur]])[node]
            && !(C.keys[C.l[cur]])[C.k[node]]
            && C.min[cur] <= C.min[C.l[cur]]
            && C.max[C.l[cur]] < C.k[cur]
        );
        invariant C.p[cur] != null && C.r[cur] != null ==> (
            !(C.repr[C.r[cur]])[node]
            && !(C.keys[C.r[cur]])[C.k[node]]
            && C.k[cur] < C.min[C.r[cur]]
            && C.max[C.r[cur]] <= C.max[cur]
        );
        invariant C.p[cur] == null && C.r[cur] != null ==> (
            !(C.repr[C.r[cur]])[node]
            && !(C.keys[C.r[cur]])[C.k[node]]
        );
        invariant (C.repr[root])[cur];
        invariant C.root[cur] == root;
        invariant C.p[cur] != null ==> C.k[cur] != C.k[node];
        invariant Unchanged(
            C.k, C.l, C.r, C.p, C.min, C.max, C.size,
            C.keys, C.repr, C.depth, C.root,
            C.k_pl0, C.l_pl0, C.r_pl0, C.p_pl0, C.min_pl0, C.max_pl0, C.size_pl0,
            C.keys_pl0, C.repr_pl0, C.depth_pl0, C.root_pl0,
            root
        );
        invariant Unchanged(
            C.k, C.l, C.r, C.p, C.min, C.max, C.size,
            C.keys, C.repr, C.depth, C.root,
            C.k_pl0, C.l_pl0, C.r_pl0, C.p_pl0, C.min_pl0, C.max_pl0, C.size_pl0,
            C.keys_pl0, C.repr_pl0, C.depth_pl0, C.root_pl0,
            node
        );
        invariant ret != null ==>
            Unchanged(
                C.k, C.l, C.r, C.p, C.min, C.max, C.size,
                C.keys, C.repr, C.depth, C.root,
                C.k_pl0, C.l_pl0, C.r_pl0, C.p_pl0, C.min_pl0, C.max_pl0, C.size_pl0,
                C.keys_pl0, C.repr_pl0, C.depth_pl0, C.root_pl0,
                ret
            );
        invariant Frame_all(
            C.k, C.l, C.r, C.p, C.min, C.max, C.size,
            C.keys, C.repr, C.depth, C.root,
            old(C.k), old(C.l), old(C.r), old(C.p), old(C.min), old(C.max), old(C.size),
            old(C.keys), old(C.repr), old(C.depth), old(C.root),
            old(C.repr)[old(C.root)[x]],
            old(alloc)
        );
    {
        // Do we have a valid termination measure?
        call t := Get_depth(cur);
        assert t >= 0;
        z := t;

        call cur_p := Get_p(cur);
        call IfNotBr_ThenLC(cur_p);
        call cur_l := Get_l(cur);
        call cur_r := Get_r(cur);
        call IfNotBr_ThenLC(cur_l);
        call IfNotBr_ThenLC(cur_r);

        call cur_k := Get_k(cur);
        call cur_l_size := GetSizeOrZero(cur_l);
        call cur_r_size := GetSizeOrZero(cur_r);
        if (cur_l != null) {
            call cur_l_min := Get_min(cur_l);
            call cur_l_keys := Get_keys(cur_l);
            call cur_l_repr := Get_repr(cur_l);
        }
        if (cur_r != null) {
            call cur_r_max := Get_max(cur_r);
            call cur_r_keys := Get_keys(cur_r);
            call cur_r_repr := Get_repr(cur_r);
        }
        call Set_size(cur, cur_l_size + 1 + cur_r_size);
        call Set_repr(
            cur,
            RefSetUnionF(
                if cur_l == null then EmptyRefSet else cur_l_repr,
                if cur_r == null then EmptyRefSet else cur_r_repr
            )[cur := true]
        );
        call Set_keys(
            cur,
            KeySetUnionF(
                if cur_l == null then EmptyKeySet else cur_l_keys,
                if cur_r == null then EmptyKeySet else cur_r_keys
            )[cur_k := true]
        );
        call Set_min(cur, if cur_l == null then cur_k else cur_l_min);
        call Set_max(cur, if cur_r == null then cur_k else cur_r_max);
        call AssertLCAndRemove(cur);

        call cur_p := Get_p(cur);
        cur := cur_p;

        call cur_p := Get_p(cur);

        // Has our termination measure decreased?
        call t := Get_depth(cur);
        assert t < z;
    }

    call cur_l := Get_l(cur);
    call cur_r := Get_r(cur);
    call IfNotBr_ThenLC(cur_l);
    call IfNotBr_ThenLC(cur_r);

    call DeleteFromRootRepr(cur, node);
    call cur_l_size := GetSizeOrZero(cur_l);
    call cur_r_size := GetSizeOrZero(cur_r);
    call Set_size(cur, cur_l_size + 1 + cur_r_size);
    if (cur_r != null) {
        call cur_r_keys := Get_keys(cur_r);
    }
    call Set_keys(cur, if cur_r == null then EmptyKeySet else cur_r_keys);
    call AssertLCAndRemove(cur);

    call IfNotBr_ThenLC(ret);
}