// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions of Data Structures"
// by Anonymous Authors.
// 
// Artifact by Anonymous Author, 2023. 
//
// Verification of deleting inside a BST, for overlaid Data Structures.

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

procedure BSTRemoveRootInsideContract(q1s: Ref, q1t: Ref, x: Ref)
    returns (ret: Ref, root: Ref);
    requires x != null;
    requires RefSetsDisjoint(
        C.bst_repr[x],
        Br_bst
    );
    requires RefSetsEqual(Br_list, EmptyRefSet);
    requires LC(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, x);
    requires C.p[x] != null;
    requires C.l[C.p[x]] == x || C.r[C.p[x]] == x;
    requires !(C.l[C.p[x]] == x && C.r[C.p[x]] == x);
    requires C.next[x] == null && C.prev[x] == null;
    requires q1s != null ==> x != q1s;
    modifies Br_bst, Br_list, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root;
    ensures root != null;
    ensures ret == null || ret == old(C.l)[x] || ret == old(C.r)[x];
    ensures (RefSetsEqual(old(C.bst_repr)[x], EmptyRefSet[x := true]) ==> ret == null);
    ensures ((RefSetSubset(EmptyRefSet[x := true], old(C.bst_repr)[x]) 
             && !RefSetsEqual(old(C.bst_repr)[x], EmptyRefSet[x := true]))
                ==> ret != null);
    ensures (ret != null ==>
                LC(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                    C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                    C.next, C.prev, C.list_keys, C.list_repr, ret)
                && KeySetsEqual(C.bst_keys[ret], (old(C.bst_keys)[x])[C.k[x] := false])
                && C.min[ret] >= old(C.min)[x]
                && C.max[ret] <= old(C.max)[x]
                && RefSetsEqual(C.bst_repr[ret], (old(C.bst_repr)[x])[x := false])
                && C.bst_root[ret] == old(C.bst_root)[x]
                && C.p[ret] == old(C.p)[x]);
    ensures old(C.l)[old(C.p)[x]] == x ==> C.l[old(C.p)[x]] == ret;
    ensures old(C.l)[old(C.p)[x]] != x ==> C.l[old(C.p)[x]] == old(C.l)[old(C.p)[x]];
    ensures old(C.r)[old(C.p)[x]] == x ==> C.r[old(C.p)[x]] == ret;
    ensures old(C.r)[old(C.p)[x]] != x ==> C.r[old(C.p)[x]] == old(C.r)[old(C.p)[x]];
    ensures old(C.k)[old(C.p)[x]] == C.k[old(C.p)[x]];
    ensures old(C.p)[old(C.p)[x]] == C.p[old(C.p)[x]];
    ensures old(C.bst_size)[old(C.p)[x]] == C.bst_size[old(C.p)[x]];
    ensures KeySetsEqual(old(C.bst_keys)[old(C.p)[x]], C.bst_keys[old(C.p)[x]]);
    ensures RefSetsEqual(old(C.bst_repr)[old(C.p)[x]], C.bst_repr[old(C.p)[x]]);
    ensures old(C.min)[old(C.p)[x]] == C.min[old(C.p)[x]];
    ensures old(C.max)[old(C.p)[x]] == C.max[old(C.p)[x]];
    ensures old(C.bst_depth)[old(C.p)[x]] == C.bst_depth[old(C.p)[x]];
    ensures old(C.bst_root)[old(C.p)[x]] == C.bst_root[old(C.p)[x]];
    ensures root == x && C.k[root] == old(C.k)[x];
    ensures LC(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, root);
    ensures BST_Isolated(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, root);
    ensures q1s != null ==> C.bst_root[q1s] == old(C.bst_root)[q1s];
    ensures old(C.p)[x] == null ==> RefSetsEqual(Br_bst, old(Br_bst));
    ensures old(C.p)[x] != null ==> RefSetsEqual(Br_bst, old(Br_bst)[old(C.p)[x] := true]);
    ensures RefSetsEqual(Br_list, EmptyRefSet);
    // Framing conditions
    ensures Frame_all(
        C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
        C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
        C.next, C.prev, C.list_keys, C.list_repr,
        old(C.k), old(C.l), old(C.r), old(C.p), old(C.min), old(C.max), old(C.bst_size),
        old(C.bst_keys), old(C.bst_repr), old(C.bst_depth), old(C.bst_root),
        old(C.next), old(C.prev), old(C.list_keys), old(C.list_repr),
        RefSetIntersectF(old(C.bst_repr)[x], old(C.bst_repr)[old(C.bst_root)[x]])[old(C.p)[x] := true],
        old(alloc)
    );

procedure BSTDeleteInside(q1s: Ref, q1t: Ref, root: Ref, x: Ref)
    returns (ret: Ref, node: Ref)
    requires root != null && x != null;
    requires RefSetsEqual(Br_bst, EmptyRefSet);
    requires RefSetsEqual(Br_list, EmptyRefSet);
    requires LC(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, x);
    requires C.p[x] != null;
    requires C.l[C.p[x]] == x || C.r[C.p[x]] == x;
    requires !(C.l[C.p[x]] == x && C.r[C.p[x]] == x);
    requires C.bst_root[x] == root;
    requires C.next[x] == null && C.prev[x] == null;
    requires q1s != null ==> x != q1s;
    modifies Br_bst, Br_list, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root;
    ensures node != null;
    ensures ret == null || ret == old(C.l)[x] || ret == old(C.r)[x];
    ensures (RefSetsEqual(old(C.bst_repr)[x], EmptyRefSet[x := true]) ==> ret == null);
    ensures ((RefSetSubset(EmptyRefSet[x := true], old(C.bst_repr)[x]) 
             && !RefSetsEqual(old(C.bst_repr)[x], EmptyRefSet[x := true]))
                ==> ret != null);
    ensures (ret != null ==>
                LC(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                    C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                    C.next, C.prev, C.list_keys, C.list_repr, ret)
                && KeySetsEqual(C.bst_keys[ret], (old(C.bst_keys)[x])[C.k[x] := false])
                && C.min[ret] >= old(C.min)[x]
                && C.max[ret] <= old(C.max)[x]
                && RefSetsEqual(C.bst_repr[ret], (old(C.bst_repr)[x])[x := false])
                && C.bst_root[ret] == root
                && C.p[ret] == old(C.p)[x]);
    ensures KeySetsEqual(C.bst_keys[root], (old(C.bst_keys)[root])[C.k[x] := false]);
    ensures C.min[root] == old(C.min)[root];
    ensures C.max[root] == old(C.max)[root];
    ensures RefSetsEqual(C.bst_repr[root], (old(C.bst_repr)[root])[x := false]);
    ensures C.bst_root[root] == old(C.bst_root)[root];
    ensures C.p[root] == old(C.p)[root];
    ensures node == x && C.k[node] == old(C.k)[x];
    ensures LC(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, node);
    ensures BST_Isolated(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, node);
    ensures q1s != null ==> C.bst_root[q1s] == old(C.bst_root)[q1s];
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
        old(C.bst_repr)[old(C.bst_root)[x]],
        old(alloc)
    );
{
    // Local variables
    var p: Ref;
    var cur: Ref;

    // Subexpressions
    var p_l: Ref; var p_r: Ref; var cur_p: Ref;
    var cur_l: Ref; var cur_r: Ref; var cur_k: int;
    var cur_l_bst_size: int; var cur_r_bst_size: int;
    var cur_l_min: int; var cur_l_bst_keys: KeySet;
    var cur_l_bst_repr: RefSet;
    var cur_r_max: int; var cur_r_bst_keys: KeySet;
    var cur_r_bst_repr: RefSet;

    // Heap value, PreLoop0:
    var C.k_pl0: [Ref]int;
    var C.l_pl0: [Ref]Ref; var C.r_pl0: [Ref]Ref;
    var C.p_pl0: [Ref]Ref; var C.min_pl0: [Ref]int; var C.max_pl0: [Ref]int;
    var C.bst_size_pl0: [Ref]int; var C.bst_keys_pl0: [Ref]KeySet; var C.bst_repr_pl0: [Ref]RefSet;
    var C.bst_depth_pl0: [Ref]int; var C.bst_root_pl0: [Ref]Ref;
    var C.next_pl0: [Ref]Ref; var C.prev_pl0: [Ref]Ref;
    var C.list_keys_pl0: [Ref]KeySet; var C.list_repr_pl0: [Ref]RefSet;

    // Loop termination
    var t: int;
    var z: int;

    call InAllocParam(q1s);
    call InAllocParam(q1t);
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
    call ret, node := BSTRemoveRootInsideContract(q1s, q1t, x);
    cur := p;

    call IfNotBrList_ThenListLC(cur);

    // label PreLoop0:
    C.k_pl0 := C.k;
    C.l_pl0 := C.l; C.r_pl0 := C.r;
    C.p_pl0 := C.p; C.min_pl0 := C.min; C.max_pl0 := C.max;
    C.bst_size_pl0 := C.bst_size; C.bst_keys_pl0 := C.bst_keys; C.bst_repr_pl0 := C.bst_repr;
    C.bst_depth_pl0 := C.bst_depth; C.bst_root_pl0 := C.bst_root;
    C.next_pl0 := C.next; C.prev_pl0 := C.prev;
    C.list_repr_pl0 := C.list_repr; C.list_keys_pl0 := C.list_keys;

    // Since this is a ghost loop, we must prove termination of it
    call cur_p := Get_p(cur);

    while (cur_p != null)
        invariant cur != null;
        invariant cur_p == C.p[cur];
        invariant RefSetsEqual(Br_bst, EmptyRefSet[cur := true]);
        invariant RefSetsEqual(Br_list, EmptyRefSet);
        invariant LC_Trans_PlusNode(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, cur, node);
        invariant (C.bst_keys[cur])[C.k[node]];
        invariant C.p[cur] != null && C.l[cur] != null ==> (
            !(C.bst_repr[C.l[cur]])[node]
            && !(C.bst_keys[C.l[cur]])[C.k[node]]
            && C.min[cur] <= C.min[C.l[cur]]
            && C.max[C.l[cur]] < C.k[cur]
        );
        invariant C.p[cur] != null && C.r[cur] != null ==> (
            !(C.bst_repr[C.r[cur]])[node]
            && !(C.bst_keys[C.r[cur]])[C.k[node]]
            && C.k[cur] < C.min[C.r[cur]]
            && C.max[C.r[cur]] <= C.max[cur]
        );
        invariant C.p[cur] == null && C.r[cur] != null ==> (
            !(C.bst_repr[C.r[cur]])[node]
            && !(C.bst_keys[C.r[cur]])[C.k[node]]
        );
        invariant (C.bst_repr[root])[cur];
        invariant C.bst_root[cur] == root;
        invariant C.p[cur] != null ==> C.k[cur] != C.k[node];
        invariant Unchanged(
            C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
            C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
            C.next, C.prev, C.list_keys, C.list_repr,
            C.k_pl0, C.l_pl0, C.r_pl0, C.p_pl0, C.min_pl0, C.max_pl0, C.bst_size_pl0,
            C.bst_keys_pl0, C.bst_repr_pl0, C.bst_depth_pl0, C.bst_root_pl0,
            C.next_pl0, C.prev_pl0, C.list_keys_pl0, C.list_repr_pl0,
            root
        );
        invariant Unchanged(
            C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
            C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
            C.next, C.prev, C.list_keys, C.list_repr,
            C.k_pl0, C.l_pl0, C.r_pl0, C.p_pl0, C.min_pl0, C.max_pl0, C.bst_size_pl0,
            C.bst_keys_pl0, C.bst_repr_pl0, C.bst_depth_pl0, C.bst_root_pl0,
            C.next_pl0, C.prev_pl0, C.list_keys_pl0, C.list_repr_pl0,
            node
        );
        invariant ret != null ==>
            Unchanged(
                C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr,
                C.k_pl0, C.l_pl0, C.r_pl0, C.p_pl0, C.min_pl0, C.max_pl0, C.bst_size_pl0,
                C.bst_keys_pl0, C.bst_repr_pl0, C.bst_depth_pl0, C.bst_root_pl0,
                C.next_pl0, C.prev_pl0, C.list_keys_pl0, C.list_repr_pl0,
                ret
            );
        invariant q1s != null ==> C.bst_root[q1s] == old(C.bst_root)[q1s];
        invariant Frame_all(
            C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
            C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
            C.next, C.prev, C.list_keys, C.list_repr,
            old(C.k), old(C.l), old(C.r), old(C.p), old(C.min), old(C.max), old(C.bst_size),
            old(C.bst_keys), old(C.bst_repr), old(C.bst_depth), old(C.bst_root),
            old(C.next), old(C.prev), old(C.list_keys), old(C.list_repr),
            old(C.bst_repr)[old(C.bst_root)[x]],
            old(alloc)
        );
    {
        // Do we have a valid termination measure?
        call t := Get_bst_depth(cur);
        assert t >= 0;
        z := t;

        call cur_p := Get_p(cur);
        call IfNotBr_ThenLC(cur_p);
        call cur_l := Get_l(cur);
        call cur_r := Get_r(cur);
        call IfNotBr_ThenLC(cur_l);
        call IfNotBr_ThenLC(cur_r);

        call cur_k := Get_k(cur);
        call cur_l_bst_size := GetBSTSizeOrZero(cur_l);
        call cur_r_bst_size := GetBSTSizeOrZero(cur_r);
        if (cur_l != null) {
            call cur_l_min := Get_min(cur_l);
            call cur_l_bst_keys := Get_bst_keys(cur_l);
            call cur_l_bst_repr := Get_bst_repr(cur_l);
        }
        if (cur_r != null) {
            call cur_r_max := Get_max(cur_r);
            call cur_r_bst_keys := Get_bst_keys(cur_r);
            call cur_r_bst_repr := Get_bst_repr(cur_r);
        }
        call Set_bst_size(cur, cur_l_bst_size + 1 + cur_r_bst_size);
        call Set_bst_repr(
            cur,
            RefSetUnionF(
                if cur_l == null then EmptyRefSet else cur_l_bst_repr,
                if cur_r == null then EmptyRefSet else cur_r_bst_repr
            )[cur := true]
        );
        call Set_bst_keys(
            cur,
            KeySetUnionF(
                if cur_l == null then EmptyKeySet else cur_l_bst_keys,
                if cur_r == null then EmptyKeySet else cur_r_bst_keys
            )[cur_k := true]
        );
        call Set_min(cur, if cur_l == null then cur_k else cur_l_min);
        call Set_max(cur, if cur_r == null then cur_k else cur_r_max);
        call AssertLCAndRemove(cur);

        call cur_p := Get_p(cur);
        cur := cur_p;

        call IfNotBrList_ThenListLC(cur);

        call cur_p := Get_p(cur);

        // Has our termination measure decreased?
        call t := Get_bst_depth(cur);
        assert t < z;
    }

    call cur_l := Get_l(cur);
    call cur_r := Get_r(cur);
    call IfNotBr_ThenLC(cur_l);
    call IfNotBr_ThenLC(cur_r);

    call DeleteFromRootRepr(cur, node);
    call cur_l_bst_size := GetBSTSizeOrZero(cur_l);
    call cur_r_bst_size := GetBSTSizeOrZero(cur_r);
    call Set_bst_size(cur, cur_l_bst_size + 1 + cur_r_bst_size);
    if (cur_r != null) {
        call cur_r_bst_keys := Get_bst_keys(cur_r);
    }
    call Set_bst_keys(cur, if cur_r == null then EmptyKeySet else cur_r_bst_keys);
    call AssertLCAndRemove(cur);

    call IfNotBr_ThenLC(ret);
}