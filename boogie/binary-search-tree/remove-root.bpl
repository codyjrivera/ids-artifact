// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions of Datastructures"
// by Anonymous Authors.
// 
// Artifact by Anonymous Author, 2023. 
//
// Verification of BST Remove Root.

procedure BSTRemoveRootContract(x: Ref)
    returns (ret: Ref, root: Ref);
    requires x != null;
    requires RefSetsDisjoint(C.repr[x], Br);
    requires LC(C.k, C.l, C.r, C.p, 
                C.min, C.max, C.keys, C.repr,
                x);
    modifies C.k, C.l, C.r, C.p,
        C.min, C.max, C.keys,
        C.repr, Br;
    ensures root != null;
    ensures ret == null || (ret == old(C.l)[x] || ret == old(C.r)[x]);
    ensures (RefSetsEqual(old(C.repr)[x], EmptyRefSet[x := true]) ==> ret == null);
    ensures ((RefSetSubset(EmptyRefSet[x := true], old(C.repr)[x]) 
             && !RefSetsEqual(old(C.repr)[x], EmptyRefSet[x := true]))
                ==> ret != null);
    ensures (ret != null ==>
                LC(C.k, C.l, C.r, C.p, 
                    C.min, C.max, C.keys, C.repr,
                    ret)
                && C.p[ret] == null
                && KeySetsEqual(C.keys[ret], (old(C.keys)[x])[C.k[x] := false])
                && C.min[ret] >= old(C.min)[x]
                && C.max[ret] <= old(C.max)[x]
                && RefSetSubset(C.repr[ret], old(C.repr)[x]));
    ensures root == x && C.k[root] == old(C.k)[x];
    ensures LC(C.k, C.l, C.r, C.p, 
                C.min, C.max, C.keys, C.repr,
                root);
    ensures Isolated(C.k, C.l, C.r, C.p, 
                    C.min, C.max, C.keys, C.repr,
                    root);
    ensures old(C.p)[x] == null ==> RefSetsEqual(Br, old(Br));
    ensures old(C.p)[x] != null ==> RefSetsEqual(Br, old(Br)[old(C.p)[x] := true]);
    // Framing conditions.
    ensures Frame_all(
        C.k, C.l, C.r, C.p,
        C.min, C.max, C.keys, C.repr,
        old(C.k), old(C.l), old(C.r), old(C.p), 
        old(C.min), old(C.max), old(C.keys), old(C.repr),
        old(C.repr)[x], old(alloc)
    );

procedure BSTRemoveRoot(x: Ref)
    returns (ret: Ref, root: Ref)
    requires x != null;
    requires RefSetsDisjoint(C.repr[x], Br);
    requires LC(C.k, C.l, C.r, C.p, 
                C.min, C.max, C.keys, C.repr,
                x);
    modifies C.k, C.l, C.r, C.p,
        C.min, C.max, C.keys,
        C.repr, Br;
    ensures root != null;
    ensures ret == null || (ret == old(C.l)[x] || ret == old(C.r)[x]);
    ensures (RefSetsEqual(old(C.repr)[x], EmptyRefSet[x := true]) ==> ret == null);
    ensures ((RefSetSubset(EmptyRefSet[x := true], old(C.repr)[x]) 
             && !RefSetsEqual(old(C.repr)[x], EmptyRefSet[x := true]))
                ==> ret != null);
    ensures (ret != null ==>
                LC(C.k, C.l, C.r, C.p, 
                    C.min, C.max, C.keys, C.repr,
                    ret)
                && C.p[ret] == null
                && KeySetsEqual(C.keys[ret], (old(C.keys)[x])[C.k[x] := false])
                && C.min[ret] >= old(C.min)[x]
                && C.max[ret] <= old(C.max)[x]
                && RefSetSubset(C.repr[ret], old(C.repr)[x]));
    ensures root == x && C.k[root] == old(C.k)[x];
    ensures LC(C.k, C.l, C.r, C.p, 
                C.min, C.max, C.keys, C.repr,
                root);
    ensures Isolated(C.k, C.l, C.r, C.p, 
                    C.min, C.max, C.keys, C.repr,
                    root);
    ensures old(C.p)[x] == null ==> RefSetsEqual(Br, old(Br));
    ensures old(C.p)[x] != null ==> RefSetsEqual(Br, old(Br)[old(C.p)[x] := true]);
    // Framing conditions.
    ensures Frame_all(
        C.k, C.l, C.r, C.p,
        C.min, C.max, C.keys, C.repr,
        old(C.k), old(C.l), old(C.r), old(C.p), 
        old(C.min), old(C.max), old(C.keys), old(C.repr),
        old(C.repr)[x], old(alloc)
    );
{
    // Local variable declarations
    var l: Ref;
    var r: Ref;
    var rl: Ref;
    var tmp: Ref;

    // Intermediate Expresssions
    var x_k: int; var x_l: Ref; var x_r: Ref;
    var x_l_min: int; var x_r_max: int; 
    var x_l_keys: KeySet; var x_l_repr: RefSet;
    var x_r_keys: KeySet; var x_r_repr: RefSet;
    var x_r_l: Ref; var x_r_r: Ref;
    var x_l_prio: int; var x_r_prio: int;
    var r_r: Ref; var r_l: Ref; var r_k: int;
    var r_r_max: int; var r_r_keys: KeySet; var r_r_repr: RefSet;
    var r_l_min: int; var r_l_keys: KeySet; var r_l_repr: RefSet;

    call InAllocParam(x);

    call x_l := Get_l(x);
    call x_r := Get_r(x);
    if (x_l == null && x_r == null) {
        call Set_p(x, null);
        call AssertLCAndRemove(x);
        ret := null; root := x;
    } else if (x_l == null) {
        call IfNotBr_ThenLC(x_r);
        r := x_r;
        call Set_p(r, null);

        call x_k := Get_k(x);
        call Set_r(x, null);
        call Set_max(x, x_k);
        call Set_keys(x, EmptyKeySet[x_k := true]);
        call Set_repr(x, EmptyRefSet[x := true]);
        call Set_p(x, null);

        call AssertLCAndRemove(r);
        call AssertLCAndRemove(x);

        ret := r; root := x;
    } else if (x_r == null) {
        call IfNotBr_ThenLC(x_l);
        l := x_l;
        call Set_p(l, null);

        call x_k := Get_k(x);
        call Set_l(x, null);
        call Set_min(x, x_k);
        call Set_keys(x, EmptyKeySet[x_k := true]);
        call Set_repr(x, EmptyRefSet[x := true]);
        call Set_p(x, null);

        call AssertLCAndRemove(l);
        call AssertLCAndRemove(x);

        ret := l; root := x;
    } else {
        call IfNotBr_ThenLC(x_l);
        call IfNotBr_ThenLC(x_r);
        call x_r_l := Get_l(x_r);
        call x_r_r := Get_r(x_r);
        call IfNotBr_ThenLC(x_r_l);
        call IfNotBr_ThenLC(x_r_r);

        call r := Get_r(x);
        call rl := Get_l(r);

        call Set_r(x, rl);
        if (rl != null) {
            call Set_p(rl, x);
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
        call Set_max(x, if x_r == null then x_k else x_r_max);
        call Set_keys(x, 
            KeySetUnionF(
                (if x_l == null then EmptyKeySet else x_l_keys)[x_k := true],
                if x_r == null then EmptyKeySet else x_r_keys
            )
        );
        call Set_repr(x, 
            RefSetUnionF(
                (if x_l == null then EmptyRefSet else x_l_repr)[x := true],
                if x_r == null then EmptyRefSet else x_r_repr
            )
        );

        call r_r := Get_r(r);
        call r_k := Get_k(r);
        if (r_r != null) {
            call r_r_keys := Get_keys(r_r);
            call r_r_repr := Get_repr(r_r);
        }
        call Set_l(r, null);
        call Set_p(r, null);
        call Set_min(r, r_k);
        call Set_keys(r, (if r_r == null then EmptyKeySet else r_r_keys)[r_k := true]);
        call Set_repr(r, (if r_r == null then EmptyRefSet else r_r_repr)[r := true]);

        call AssertLCAndRemove(x);
        call AssertLCAndRemove(rl);
        call AssertLCAndRemove(r);

        call tmp, root := BSTRemoveRootContract(x);

        call Set_l(r, tmp);
        if (tmp != null) {
            call Set_p(tmp, r);
        }
        call Set_p(r, null);

        call r_l := Get_l(r);
        call r_r := Get_r(r);
        call r_k := Get_k(r);
        if (r_l != null) {
            call r_l_min := Get_min(r_l);
            call r_l_keys := Get_keys(r_l);
            call r_l_repr := Get_repr(r_l);
        }
        if (r_r != null) {
            call r_r_max := Get_max(r_r);
            call r_r_keys := Get_keys(r_r);
            call r_r_repr := Get_repr(r_r);
        }
        call Set_min(r, if r_l == null then r_k else r_l_min);
        call Set_max(r, if r_r == null then r_k else r_r_max);
        call Set_keys(r, 
            KeySetUnionF(
                (if r_l == null then EmptyKeySet else r_l_keys)[r_k := true],
                if r_r == null then EmptyKeySet else r_r_keys
            )
        );
        call Set_repr(r, 
            RefSetUnionF(
                (if r_l == null then EmptyRefSet else r_l_repr)[r := true],
                if r_r == null then EmptyRefSet else r_r_repr
            )
        );
        
        call AssertLCAndRemove(r);
        call AssertLCAndRemove(r_l);

        ret := r;
    }
}