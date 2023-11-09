// Supporting Artifact for
// "Predictive Verification using Intrinsic Definitions of Data Structures"
// by Adithya Murali, Cody Rivera, and P. Madhusudan.
// 
// Artifact by Cody Rivera, 2023. 
//
// Verification of interior BST Remove Root, for overlaid data structures.

procedure BSTFixDepthContract(q1s: Ref, q1t: Ref, x: Ref);
    requires x != null;
    requires RefSetsDisjoint(
        (C.bst_repr[x])[x := false],
        Br_bst
    );
    requires RefSetsEqual(Br_list, EmptyRefSet);
    requires LC_Trans_NoDepth(C.k, C.l, C.r, C.p, C.min, C.max,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, x);
    requires C.p[x] != null;
    modifies Br_bst, Br_list, C.bst_depth;
    ensures LC(C.k, C.l, C.r, C.p, C.min, C.max,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, x);
    ensures RefSetsEqual(Br_bst, old(Br_bst)[x := false]);
    ensures RefSetsEqual(Br_list, EmptyRefSet);
    // Framing conditions
    ensures Frame_all(
        C.k, C.l, C.r, C.p, C.min, C.max,
        C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
        C.next, C.prev, C.list_keys, C.list_repr,
        old(C.k), old(C.l), old(C.r), old(C.p), old(C.min), old(C.max),
        old(C.bst_keys), old(C.bst_repr), old(C.bst_depth), old(C.bst_root),
        old(C.next), old(C.prev), old(C.list_keys), old(C.list_repr),
        RefSetIntersectF(old(C.bst_repr)[x], old(C.bst_repr)[old(C.bst_root)[x]]), old(alloc)
    );

procedure BSTRemoveRootInsideContract(q1s: Ref, q1t: Ref, x: Ref, k: int)
    returns (ret: Ref, root: Ref);
    requires x != null;
    requires RefSetsDisjoint(
        C.bst_repr[x],
        Br_bst
    );
    requires RefSetsEqual(Br_list, EmptyRefSet);
    requires LC(C.k, C.l, C.r, C.p, C.min, C.max,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, x);
    requires C.p[x] != null;
    requires C.l[C.p[x]] == x || C.r[C.p[x]] == x;
    requires !(C.l[C.p[x]] == x && C.r[C.p[x]] == x);
    requires C.next[x] == null && C.prev[x] == null;
    requires q1s != null ==> x != q1s;
    modifies Br_bst, Br_list, C.l, C.r, C.p, C.min, C.max,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root;
    ensures root != null;
    ensures ret == null || ret == old(C.l)[x] || ret == old(C.r)[x];
    ensures (RefSetsEqual(old(C.bst_repr)[x], EmptyRefSet[x := true]) ==> ret == null);
    ensures (!RefSetsEqual(old(C.bst_repr)[x], EmptyRefSet[x := true]) // TODO:?
                ==> ret != null);
    ensures (ret != null ==>
                LC(C.k, C.l, C.r, C.p, C.min, C.max,
                    C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                    C.next, C.prev, C.list_keys, C.list_repr, ret)
                && KeySetsEqual(C.bst_keys[ret], (old(C.bst_keys)[x])[C.k[x] := false])
                && C.min[ret] >= old(C.min)[x]
                && C.max[ret] <= old(C.max)[x]
                && RefSetsEqual(C.bst_repr[ret], (old(C.bst_repr)[x])[x := false])
                && C.bst_root[ret] == old(C.bst_root)[x]
                && C.p[ret] == old(C.p)[x]
                // && listfieldsunchanged(ret)
                );
    ensures old(C.l)[old(C.p)[x]] == x ==> C.l[old(C.p)[x]] == ret;
    ensures old(C.l)[old(C.p)[x]] != x ==> C.l[old(C.p)[x]] == old(C.l)[old(C.p)[x]];
    ensures old(C.r)[old(C.p)[x]] == x ==> C.r[old(C.p)[x]] == ret;
    ensures old(C.r)[old(C.p)[x]] != x ==> C.r[old(C.p)[x]] == old(C.r)[old(C.p)[x]];
    ensures old(C.k)[old(C.p)[x]] == C.k[old(C.p)[x]];
    ensures old(C.p)[old(C.p)[x]] == C.p[old(C.p)[x]];
    ensures KeySetsEqual(old(C.bst_keys)[old(C.p)[x]], C.bst_keys[old(C.p)[x]]);
    ensures RefSetsEqual(old(C.bst_repr)[old(C.p)[x]], C.bst_repr[old(C.p)[x]]);
    ensures old(C.min)[old(C.p)[x]] == C.min[old(C.p)[x]];
    ensures old(C.max)[old(C.p)[x]] == C.max[old(C.p)[x]];
    ensures old(C.bst_depth)[old(C.p)[x]] == C.bst_depth[old(C.p)[x]];
    ensures old(C.bst_root)[old(C.p)[x]] == C.bst_root[old(C.p)[x]];
    // ensures listfieldsunchanged(old(x.p));
    ensures root == x && C.k[root] == old(C.k)[x];
    ensures LC(C.k, C.l, C.r, C.p, C.min, C.max,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, root);
    ensures BST_Isolated(C.k, C.l, C.r, C.p, C.min, C.max,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, root);
    // ensures listfieldsunchanged(root);
    ensures q1s != null ==> C.bst_root[q1s] == old(C.bst_root)[q1s];
    ensures old(C.p)[x] == null ==> RefSetsEqual(Br_bst, old(Br_bst));
    ensures old(C.p)[x] != null ==> RefSetsEqual(Br_bst, old(Br_bst)[old(C.p)[x] := true]);
    ensures RefSetsEqual(Br_list, EmptyRefSet);
    // Framing conditions
    ensures Frame_all(
        C.k, C.l, C.r, C.p, C.min, C.max,
        C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
        C.next, C.prev, C.list_keys, C.list_repr,
        old(C.k), old(C.l), old(C.r), old(C.p), old(C.min), old(C.max),
        old(C.bst_keys), old(C.bst_repr), old(C.bst_depth), old(C.bst_root),
        old(C.next), old(C.prev), old(C.list_keys), old(C.list_repr),
        RefSetIntersectF(old(C.bst_repr)[x], old(C.bst_repr)[old(C.bst_root)[x]])[old(C.p)[x] := true],
        old(alloc)
    );

procedure BSTRemoveRootInside(q1s: Ref, q1t: Ref, x: Ref, k: int)
    returns (ret: Ref, root: Ref)
    requires x != null;
    requires RefSetsDisjoint(
        C.bst_repr[x],
        Br_bst
    );
    requires RefSetsEqual(Br_list, EmptyRefSet);
    requires LC(C.k, C.l, C.r, C.p, C.min, C.max,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, x);
    requires C.p[x] != null;
    requires C.l[C.p[x]] == x || C.r[C.p[x]] == x;
    requires !(C.l[C.p[x]] == x && C.r[C.p[x]] == x);
    requires C.next[x] == null && C.prev[x] == null;
    requires q1s != null ==> x != q1s;
    modifies Br_bst, Br_list, C.l, C.r, C.p, C.min, C.max,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root;
    ensures root != null;
    ensures ret == null || ret == old(C.l)[x] || ret == old(C.r)[x];
    ensures (RefSetsEqual(old(C.bst_repr)[x], EmptyRefSet[x := true]) ==> ret == null);
    ensures (!RefSetsEqual(old(C.bst_repr)[x], EmptyRefSet[x := true]) // TODO:?
                ==> ret != null);
    ensures (ret != null ==>
                LC(C.k, C.l, C.r, C.p, C.min, C.max,
                    C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                    C.next, C.prev, C.list_keys, C.list_repr, ret)
                && KeySetsEqual(C.bst_keys[ret], (old(C.bst_keys)[x])[C.k[x] := false])
                && C.min[ret] >= old(C.min)[x]
                && C.max[ret] <= old(C.max)[x]
                && RefSetsEqual(C.bst_repr[ret], (old(C.bst_repr)[x])[x := false])
                && C.bst_root[ret] == old(C.bst_root)[x]
                && C.p[ret] == old(C.p)[x]
                // && listfieldsunchanged(ret)
                );
    ensures old(C.l)[old(C.p)[x]] == x ==> C.l[old(C.p)[x]] == ret;
    ensures old(C.l)[old(C.p)[x]] != x ==> C.l[old(C.p)[x]] == old(C.l)[old(C.p)[x]];
    ensures old(C.r)[old(C.p)[x]] == x ==> C.r[old(C.p)[x]] == ret;
    ensures old(C.r)[old(C.p)[x]] != x ==> C.r[old(C.p)[x]] == old(C.r)[old(C.p)[x]];
    ensures old(C.k)[old(C.p)[x]] == C.k[old(C.p)[x]];
    ensures old(C.p)[old(C.p)[x]] == C.p[old(C.p)[x]];
    ensures KeySetsEqual(old(C.bst_keys)[old(C.p)[x]], C.bst_keys[old(C.p)[x]]);
    ensures RefSetsEqual(old(C.bst_repr)[old(C.p)[x]], C.bst_repr[old(C.p)[x]]);
    ensures old(C.min)[old(C.p)[x]] == C.min[old(C.p)[x]];
    ensures old(C.max)[old(C.p)[x]] == C.max[old(C.p)[x]];
    ensures old(C.bst_depth)[old(C.p)[x]] == C.bst_depth[old(C.p)[x]];
    ensures old(C.bst_root)[old(C.p)[x]] == C.bst_root[old(C.p)[x]];
    // ensures listfieldsunchanged(old(x.p));
    ensures root == x && C.k[root] == old(C.k)[x];
    ensures LC(C.k, C.l, C.r, C.p, C.min, C.max,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, root);
    ensures BST_Isolated(C.k, C.l, C.r, C.p, C.min, C.max,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, root);
    // ensures listfieldsunchanged(root);
    ensures q1s != null ==> C.bst_root[q1s] == old(C.bst_root)[q1s];
    ensures old(C.p)[x] == null ==> RefSetsEqual(Br_bst, old(Br_bst));
    ensures old(C.p)[x] != null ==> RefSetsEqual(Br_bst, old(Br_bst)[old(C.p)[x] := true]);
    ensures RefSetsEqual(Br_list, EmptyRefSet);
    // Framing conditions
    ensures Frame_all(
        C.k, C.l, C.r, C.p, C.min, C.max,
        C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
        C.next, C.prev, C.list_keys, C.list_repr,
        old(C.k), old(C.l), old(C.r), old(C.p), old(C.min), old(C.max),
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

    // Subexpressions
    var x_l: Ref;
    var x_r: Ref;
    var x_k: int;
    var p_l: Ref;
    var x_r_l: Ref;
    var x_r_r: Ref;

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

        assume false;
    }

}


    