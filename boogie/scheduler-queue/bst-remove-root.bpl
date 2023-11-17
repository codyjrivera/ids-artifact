// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions of Data Structures"
// by Anonymous Authors.
// 
// Artifact by Anonymous Author, 2023. 
//
// Verification of interior BST Remove Root, for overlaid Data Structures.

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

procedure BSTRemoveRootInside(q1s: Ref, q1t: Ref, x: Ref)
    returns (ret: Ref, root: Ref)
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
{
    // Local variables
    var p: Ref;
    var r: Ref;
    var l: Ref;
    var rl: Ref;
    var fix_p_l: bool;
    var fix_p_r: bool;
    var tmp: Ref;

    // Subexpressions
    var x_l: Ref;
    var x_r: Ref;
    var x_k: int;
    var p_l: Ref;
    var x_r_l: Ref;
    var x_r_r: Ref;
    var r_l: Ref;
    var x_l_bst_keys: KeySet;
    var x_l_bst_repr: RefSet;
    var x_r_max: int;
    var x_r_bst_keys: KeySet;
    var x_r_bst_repr: RefSet;
    var r_r: Ref;
    var r_k: int;
    var x_p: Ref;
    var r_r_bst_keys: KeySet;
    var r_r_bst_repr: RefSet;
    var p_r: Ref;
    var r_l_min: int;
    var r_l_bst_keys: KeySet;
    var r_l_bst_repr: RefSet;
    var r_p: Ref;
    var r_p_bst_depth: int;
    var x_l_bst_size: int;
    var x_r_bst_size: int;
    var r_l_bst_size: int;
    var r_r_bst_size: int;

    call InAllocParam(q1s);
    call InAllocParam(q1t);
    call InAllocParam(x);
    
    call p := Get_p(x);
    call x_l := Get_l(x);
    call x_r := Get_r(x);
    if (x_l == null && x_r == null) {
        call Set_bst_root(x, x);
        call Set_bst_depth(x, 0);
        call Set_bst_keys(x, EmptyKeySet);
        call Set_p(x, null);

        call p_l := Get_l(p);
        if (p_l == x) {
            call Set_l(p, null);
        } else {
            call Set_r(p, null);
        }
        call AssertLCAndRemove(x);

        ret := null;
        root := x;
    } else if (x_l == null) {
        call IfNotBr_ThenLC(x_r);
        r := x_r;

        call Set_r(x, null);
        call x_k := Get_k(x);
        call Set_max(x, x_k);
        call Set_bst_keys(x, EmptyKeySet);
        call Set_bst_size(x, 1);
        call Set_bst_repr(x, EmptyRefSet[x := true]);
        call Set_bst_root(x, x);
        call Set_bst_depth(x, 0);
        call Set_p(x, null);
        call AssertLCAndRemove(x);

        call Set_p(r, p);
        if (p != null) {
            call p_l := Get_l(p);
            if (p_l == x) {
                call Set_l(p, r);
            } else {
                call Set_r(p, r);
            }
            call AssertLCAndRemove(x);
        }

        call BSTFixDepthContract(q1s, q1t, r);
        call AssertLCAndRemove(r);

        ret := r;
        root := x;
    } else if (x_r == null) {
        call IfNotBr_ThenLC(x_l);
        l := x_l;

        call Set_l(x, null);
        call x_k := Get_k(x);
        call Set_max(x, x_k);
        call Set_bst_keys(x, EmptyKeySet);
        call Set_bst_size(x, 1);
        call Set_bst_repr(x, EmptyRefSet[x := true]);
        call Set_bst_root(x, x);
        call Set_bst_depth(x, 0);
        call Set_p(x, null);
        call AssertLCAndRemove(x);

        call Set_p(l, p);
        if (p != null) {
            call p_l := Get_l(p);
            if (p_l == x) {
                call Set_l(p, l);
            } else {
                call Set_r(p, l);
            }
            call AssertLCAndRemove(x);
        }

        call BSTFixDepthContract(q1s, q1t, l);
        call AssertLCAndRemove(l);

        ret := l;
        root := x;
    } else {
        call IfNotBr_ThenLC(x_l);
        call IfNotBr_ThenLC(x_r);
        
        call x_r_l := Get_l(x_r);
        call x_r_r := Get_r(x_r);

        if (x_r_l != null) {
            call IfNotBr_ThenLC(x_r_l);
        }
        if (x_r_r != null) {
            call IfNotBr_ThenLC(x_r_r);
        }
        
        call x_r := Get_r(x);
        r := x_r;
        call r_l := Get_l(r);
        rl := r_l;

        call Set_r(x, rl);
        if (rl != null) {
            call Set_p(rl, x);
            call BSTFixDepthContract(q1s, q1t, rl);
        }

        call x_l := Get_l(x);
        call x_r := Get_r(x);
        call x_k := Get_k(x);
        if (x_l != null) {
            call x_l_bst_keys := Get_bst_keys(x_l);
            call x_l_bst_repr := Get_bst_repr(x_l);
        }
        if (x_r != null) {
            call x_r_max := Get_max(x_r);
            call x_r_bst_keys := Get_bst_keys(x_r);
            call x_r_bst_repr := Get_bst_repr(x_r);
        }
        call x_l_bst_size := GetBSTSizeOrZero(x_l);
        call x_r_bst_size := GetBSTSizeOrZero(x_r);
        call Set_max(x, if x_r == null then x_k else x_r_max);
        call Set_bst_size(x, x_l_bst_size + 1 + x_r_bst_size);
        call Set_bst_keys(x, KeySetUnionF(x_l_bst_keys, if x_r == null then EmptyKeySet else x_r_bst_keys)[x_k := true]);
        call Set_bst_repr(x, RefSetUnionF(x_l_bst_repr, if x_r == null then EmptyRefSet else x_r_bst_repr)[x := true]);

        call r_r := Get_r(r);
        call r_k := Get_k(r);
        call x_p := Get_p(x);
        if (r_r != null) {
            call r_r_bst_keys := Get_bst_keys(r_r);
            call r_r_bst_repr := Get_bst_repr(r_r);
        }
        call r_r_bst_size := GetBSTSizeOrZero(r_r);
        call Set_l(r, null);
        call Set_p(r, x_p);
        call Set_min(r, r_k);
        call Set_bst_size(r, 1 + r_r_bst_size);
        call Set_bst_keys(r, (if r_r == null then EmptyKeySet else r_r_bst_keys)[r_k := true]);
        call Set_bst_repr(r, (if r_r == null then EmptyRefSet else r_r_bst_repr)[r := true]);

        call AssertLCAndRemove(x);
        call AssertLCAndRemove(rl);

        call p_l := Get_l(p);
        call p_r := Get_r(p);

        // Awkward change to non-ghost code.
        fix_p_l := p_l == x;
        fix_p_r := p_r == x;

        call tmp, root := BSTRemoveRootInsideContract(q1s, q1t, x);

        call Set_l(r, tmp);
        if (tmp != null) {
            call Set_p(tmp, r);
        }
        call Set_p(r, p);
        if (fix_p_l) {
            call Set_l(p, r);
        }
        if (fix_p_r) {
            call Set_r(p, r);
        }

        call r_l := Get_l(r);
        call r_r := Get_r(r);
        call r_k := Get_k(r);
        if (r_l != null) {
            call r_l_min := Get_min(r_l);
            call r_l_bst_keys := Get_bst_keys(r_l);
            call r_l_bst_repr := Get_bst_repr(r_l);
        }
        if (r_r != null) {
            call r_r_bst_keys := Get_bst_keys(r_r);
            call r_r_bst_repr := Get_bst_repr(r_r);
        }
        call r_l_bst_size := GetBSTSizeOrZero(r_l);
        call r_r_bst_size := GetBSTSizeOrZero(r_r);
        call r_p := Get_p(r);
        call r_p_bst_depth := Get_bst_depth(r_p);
        call Set_min(r, if r_l == null then r_k else r_l_min);
        call Set_bst_size(r, r_l_bst_size + 1 + r_r_bst_size);
        call Set_bst_keys(
            r,
            KeySetUnionF(
                if r_l == null then EmptyKeySet else r_l_bst_keys,
                if r_r == null then EmptyKeySet else r_r_bst_keys
            )[r_k := true]
        );
        call Set_bst_repr(
            r,
            RefSetUnionF(
                if r_l == null then EmptyRefSet else r_l_bst_repr,
                if r_r == null then EmptyRefSet else r_r_bst_repr
            )[r := true]
        );
        call Set_bst_depth(
            r,
            1 + r_p_bst_depth
        );

        call r_l := Get_l(r);
        call IfNotBrList_ThenListLC(r_l);
        call BSTFixDepthContract(q1s, q1t, r_l);
        call r_r := Get_r(r);
        if (r_r != null) {
            call IfNotBrList_ThenListLC(r_r);
            call BSTFixDepthContract(q1s, q1t, r_r);
        }
        call IfNotBrList_ThenListLC(r_l);
        call AssertLCAndRemove(r_l);
        call AssertLCAndRemove(r_r);
        call IfNotBrList_ThenListLC(r);
        call AssertLCAndRemove(r);

        ret := r;
    }

}


    