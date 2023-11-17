// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions of Data Structures"
// by Anonymous Authors.
// 
// Artifact by Anonymous Author, 2023. 
//
// Verification of BST Delete.

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

procedure BSTDeleteContract(x: Ref, k: int) 
    returns (ret: Ref, del: Ref);
    requires x != null;
    requires RefSetsEqual(Br, EmptyRefSet);
    requires LC(C.k, C.l, C.r, C.p, 
                C.min, C.max, C.keys, C.repr,
                x);
    modifies Br, C.k, C.l, C.r, C.p,
                C.min, C.max, C.keys, C.repr;
    ensures ret == null || ret == x || ret == old(C.l)[x] || ret == old(C.r)[x];
    ensures C.p[x] == null;
    ensures (ret == null ==>
                KeySetsEqual(old(C.keys)[x], EmptyKeySet[k := true])
                && del != null);
    ensures (ret != null ==>
                LC(C.k, C.l, C.r, C.p, 
                    C.min, C.max, C.keys, C.repr,
                    ret)
                && C.p[ret] == null
                && (del != null ==> 
                        C.p[ret] == null
                        && KeySetsEqual(C.keys[ret], (old(C.keys)[x])[k := false])
                        && C.min[ret] >= old(C.min)[x]
                        && C.max[ret] <= old(C.max)[x]
                        && RefSetSubset(C.repr[ret], old(C.repr)[x]))
                && (del == null ==>
                        KeySetsEqual(C.keys[ret], old(C.keys)[x])
                        && C.min[ret] == old(C.min)[x]
                        && C.max[ret] == old(C.max)[x]
                        && RefSetsEqual(C.repr[ret], old(C.repr)[x])));
    ensures del != null ==> C.k[del] == k && (old(C.keys)[x])[k];
    ensures del != null ==> (
        LC(C.k, C.l, C.r, C.p, 
            C.min, C.max, C.keys, C.repr,
            del)
        && Isolated(C.k, C.l, C.r, C.p,
            C.min, C.max, C.keys, C.repr,
            del)
    );
    ensures old(C.p)[x] == null ==> RefSetsEqual(Br, EmptyRefSet);
    ensures old(C.p)[x] != null ==> RefSetsEqual(Br, EmptyRefSet[old(C.p)[x] := true]);
    // Framing conditions.
    ensures Frame_all(
        C.k, C.l, C.r, C.p,
        C.min, C.max, C.keys, C.repr,
        old(C.k), old(C.l), old(C.r), old(C.p), 
        old(C.min), old(C.max), old(C.keys), old(C.repr),
        old(C.repr)[x], old(alloc)
    );

procedure BSTDelete(x: Ref, k: int) 
    returns (ret: Ref, del: Ref)
    requires x != null;
    requires RefSetsEqual(Br, EmptyRefSet);
    requires LC(C.k, C.l, C.r, C.p, 
                C.min, C.max, C.keys, C.repr,
                x);
    modifies Br, C.k, C.l, C.r, C.p,
                C.min, C.max, C.keys, C.repr;
    ensures ret == null || ret == x || ret == old(C.l)[x] || ret == old(C.r)[x];
    ensures C.p[x] == null;
    ensures (ret == null ==>
                KeySetsEqual(old(C.keys)[x], EmptyKeySet[k := true])
                && del != null);
    ensures (ret != null ==>
                LC(C.k, C.l, C.r, C.p, 
                    C.min, C.max, C.keys, C.repr,
                    ret)
                && C.p[ret] == null
                && (del != null ==> 
                        C.p[ret] == null
                        && KeySetsEqual(C.keys[ret], (old(C.keys)[x])[k := false])
                        && C.min[ret] >= old(C.min)[x]
                        && C.max[ret] <= old(C.max)[x]
                        && RefSetSubset(C.repr[ret], old(C.repr)[x]))
                && (del == null ==>
                        KeySetsEqual(C.keys[ret], old(C.keys)[x])
                        && C.min[ret] == old(C.min)[x]
                        && C.max[ret] == old(C.max)[x]
                        && RefSetsEqual(C.repr[ret], old(C.repr)[x])));
    ensures del != null ==> C.k[del] == k && (old(C.keys)[x])[k];
    ensures del != null ==> (
        LC(C.k, C.l, C.r, C.p, 
            C.min, C.max, C.keys, C.repr,
            del)
        && Isolated(C.k, C.l, C.r, C.p,
            C.min, C.max, C.keys, C.repr,
            del)
    );
    ensures old(C.p)[x] == null ==> RefSetsEqual(Br, EmptyRefSet);
    ensures old(C.p)[x] != null ==> RefSetsEqual(Br, EmptyRefSet[old(C.p)[x] := true]);
    // Framing conditions.
    ensures Frame_all(
        C.k, C.l, C.r, C.p,
        C.min, C.max, C.keys, C.repr,
        old(C.k), old(C.l), old(C.r), old(C.p), 
        old(C.min), old(C.max), old(C.keys), old(C.repr),
        old(C.repr)[x], old(alloc)
    );
{
    // Local variables
    var l: Ref;
    var r: Ref;

    // Subexpressions
    var x_l: Ref; var x_r: Ref; var x_k: int;
    var x_l_min: int; var x_r_max: int; 
    var x_l_keys: KeySet; var x_l_repr: RefSet;
    var x_r_keys: KeySet; var x_r_repr: RefSet;
    var old_x_l: Ref; var old_x_r: Ref;
    
    call InAllocParam(x);

    call x_k := Get_k(x);
    call x_l := Get_l(x);
    call x_r := Get_r(x);
    old_x_l := x_l;
    old_x_r := x_r;
    if (x_k == k) {
        call ret, del := BSTRemoveRootContract(x);
    } else if (k < x_k && x_l != null) {
        call IfNotBr_ThenLC(x_l);
        call IfNotBr_ThenLC(x_r);

        call l, del := BSTDeleteContract(x_l, k);
        call x_l := Get_l(x);
        call IfNotBr_ThenLC(x_l);

        call Set_l(x, l);
        if (l != null) {
            call Set_p(l, x);
        }
        call Set_p(x, null);

        call x_l := Get_l(x);
        call x_r := Get_r(x);
        call x_k := Get_k(x);
        if (x_l != null) {
            call x_l_min := Get_min(x_l);
            call x_l_keys := Get_keys(x_l);
            call x_l_repr := Get_repr(x_l);
        }
        if (x_r != null) {
            call x_r_keys := Get_keys(x_r);
            call x_r_repr := Get_repr(x_r);
        }
        call Set_min(x, if x_l == null then x_k else x_l_min);
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

        call AssertLCAndRemove(x);
        call AssertLCAndRemove(l);
        call AssertLCAndRemove(old_x_l);

        ret := x;
    } else if (k > x_k && x_r != null) {
        call IfNotBr_ThenLC(x_l);
        call IfNotBr_ThenLC(x_r);

        call r, del := BSTDeleteContract(x_r, k);
        call x_r := Get_r(x);
        call IfNotBr_ThenLC(x_r);

        call Set_r(x, r);
        if (r != null) {
            call Set_p(r, x);
        }
        call Set_p(x, null);

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

        call AssertLCAndRemove(x);
        call AssertLCAndRemove(r);
        call AssertLCAndRemove(old_x_r);

        ret := x;
    } else {
        call Set_p(x, null);
        call AssertLCAndRemove(x);
        ret := x; del := null;
    }
}