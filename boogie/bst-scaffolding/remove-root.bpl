// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions"
// by Adithya Murali, Cody Rivera, and P. Madhusudan.
// 
// Artifact by Cody Rivera, 2023-2024. 
//
// Verification of interior BST Remove Root, for BSTs with scaffolding.

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

procedure BSTRemoveRootInside(x: Ref)
    returns (ret: Ref, root: Ref)
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
    var x_l_keys: KeySet;
    var x_l_repr: RefSet;
    var x_r_max: int;
    var x_r_keys: KeySet;
    var x_r_repr: RefSet;
    var r_r: Ref;
    var r_k: int;
    var x_p: Ref;
    var r_r_keys: KeySet;
    var r_r_repr: RefSet;
    var p_r: Ref;
    var r_l_min: int;
    var r_l_keys: KeySet;
    var r_l_repr: RefSet;
    var r_p: Ref;
    var r_p_depth: int;
    var x_l_size: int;
    var x_r_size: int;
    var r_l_size: int;
    var r_r_size: int;

    call InAllocParam(x);
    
    call p := Get_p(x);
    call x_l := Get_l(x);
    call x_r := Get_r(x);
    if (x_l == null && x_r == null) {
        call Set_root(x, x);
        call Set_depth(x, 0);
        call Set_keys(x, EmptyKeySet);
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
        call Set_keys(x, EmptyKeySet);
        call Set_size(x, 1);
        call Set_repr(x, EmptyRefSet[x := true]);
        call Set_root(x, x);
        call Set_depth(x, 0);
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

        call BSTFixDepthContract(r);
        call AssertLCAndRemove(r);

        ret := r;
        root := x;
    } else if (x_r == null) {
        call IfNotBr_ThenLC(x_l);
        l := x_l;

        call Set_l(x, null);
        call x_k := Get_k(x);
        call Set_max(x, x_k);
        call Set_keys(x, EmptyKeySet);
        call Set_size(x, 1);
        call Set_repr(x, EmptyRefSet[x := true]);
        call Set_root(x, x);
        call Set_depth(x, 0);
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

        call BSTFixDepthContract(l);
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
            call BSTFixDepthContract(rl);
        }

        call x_l := Get_l(x);
        call x_r := Get_r(x);
        call x_k := Get_k(x);
        if (x_l != null) {
            call x_l_keys := Get_keys(x_l);
            call x_l_repr := Get_repr(x_l);
        }
        if (x_r != null) {
            call x_r_max := Get_max(x_r);
            call x_r_keys := Get_keys(x_r);
            call x_r_repr := Get_repr(x_r);
        }
        call x_l_size := GetSizeOrZero(x_l);
        call x_r_size := GetSizeOrZero(x_r);
        call Set_max(x, if x_r == null then x_k else x_r_max);
        call Set_size(x, x_l_size + 1 + x_r_size);
        call Set_keys(x, KeySetUnionF(x_l_keys, if x_r == null then EmptyKeySet else x_r_keys)[x_k := true]);
        call Set_repr(x, RefSetUnionF(x_l_repr, if x_r == null then EmptyRefSet else x_r_repr)[x := true]);

        call r_r := Get_r(r);
        call r_k := Get_k(r);
        call x_p := Get_p(x);
        if (r_r != null) {
            call r_r_keys := Get_keys(r_r);
            call r_r_repr := Get_repr(r_r);
        }
        call r_r_size := GetSizeOrZero(r_r);
        call Set_l(r, null);
        call Set_p(r, x_p);
        call Set_min(r, r_k);
        call Set_size(r, 1 + r_r_size);
        call Set_keys(r, (if r_r == null then EmptyKeySet else r_r_keys)[r_k := true]);
        call Set_repr(r, (if r_r == null then EmptyRefSet else r_r_repr)[r := true]);

        call AssertLCAndRemove(x);
        call AssertLCAndRemove(rl);

        call p_l := Get_l(p);
        call p_r := Get_r(p);

        // Awkward change to non-ghost code.
        fix_p_l := p_l == x;
        fix_p_r := p_r == x;

        call tmp, root := BSTRemoveRootInsideContract(x);

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
            call r_l_keys := Get_keys(r_l);
            call r_l_repr := Get_repr(r_l);
        }
        if (r_r != null) {
            call r_r_keys := Get_keys(r_r);
            call r_r_repr := Get_repr(r_r);
        }
        call r_l_size := GetSizeOrZero(r_l);
        call r_r_size := GetSizeOrZero(r_r);
        call r_p := Get_p(r);
        call r_p_depth := Get_depth(r_p);
        call Set_min(r, if r_l == null then r_k else r_l_min);
        call Set_size(r, r_l_size + 1 + r_r_size);
        call Set_keys(
            r,
            KeySetUnionF(
                if r_l == null then EmptyKeySet else r_l_keys,
                if r_r == null then EmptyKeySet else r_r_keys
            )[r_k := true]
        );
        call Set_repr(
            r,
            RefSetUnionF(
                if r_l == null then EmptyRefSet else r_l_repr,
                if r_r == null then EmptyRefSet else r_r_repr
            )[r := true]
        );
        call Set_depth(
            r,
            1 + r_p_depth
        );

        call r_l := Get_l(r);
        call BSTFixDepthContract(r_l);
        call r_r := Get_r(r);
        if (r_r != null) {
            call BSTFixDepthContract(r_r);
        }
        call AssertLCAndRemove(r_l);
        call AssertLCAndRemove(r_r);
        call AssertLCAndRemove(r);

        ret := r;
    }

}
