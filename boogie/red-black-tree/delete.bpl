// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions"
// by Adithya Murali, Cody Rivera, and P. Madhusudan.
// 
// Artifact by Cody Rivera, 2023-2024. 
//
// Verification of Red-Black Tree Delete.

procedure RBTFindMinContract(x: Ref) returns (ret: int);
    requires x != null;
    requires RefSetsDisjoint(Br, C.repr[x]);
    requires LC(C.k, C.l, C.r, C.p, 
                C.min, C.max, C.keys,
                C.repr, C.black, C.black_height, 
                x);
    ensures (C.keys[x])[ret];
    ensures ret == C.min[x];

procedure RBTDeleteLeftFixupContract(x: Ref) 
    returns (ret: Ref, fixed: bool);
    requires x != null;
    requires RefSetsDisjoint(Br, (C.repr[x])[x := false]);
    requires LC_Trans_DoubleBlack(C.k, C.l, C.r, C.p, 
                C.min, C.max, C.keys,
                C.repr, C.black, C.black_height, 
                x);
    requires (C.l[x] == null && C.r[x] != null && C.black_height[C.r[x]] == 1)
            || (C.l[x] != null && C.r[x] != null && C.black_height[C.l[x]] + 1 == C.black_height[C.r[x]]);
    requires (C.l[x] == null || C.black[C.l[x]]);
    requires (C.black[x] || (C.r[x] == null || C.black[C.r[x]]));
    modifies Br, C.k, C.l, C.r, C.p, 
                C.min, C.max, C.keys,
                C.repr, C.black, C.black_height;
    ensures ret != null;
    ensures x != ret ==> (
        C.p[x] != null
        && C.p[x] != old(C.p)[x]
        && (C.repr[ret])[C.p[x]]
        && (C.l[x] != null ==> (C.repr[ret])[C.l[x]])
        && (C.r[x] != null ==> (C.repr[ret])[C.r[x]])
    );
    ensures LC(C.k, C.l, C.r, C.p, 
                C.min, C.max, C.keys,
                C.repr, C.black, C.black_height, 
                ret);
    ensures C.p[ret] == null;
    ensures KeySetsEqual(C.keys[ret], old(C.keys)[x]);
    ensures C.min[ret] == old(C.min)[x];
    ensures C.max[ret] == old(C.max)[x];
    ensures RefSetsEqual(C.repr[ret], old(C.repr)[x]);
    ensures C.black[ret] || (!C.black[ret] && !old(C.black)[x]);
    ensures (fixed && C.black_height[ret] == old(C.black_height)[x])
            ||  (!fixed && old(C.black)[x] && C.black_height[ret] == old(C.black_height)[x] - 1);
    ensures old(C.p)[x] == null ==> RefSetsEqual(Br, old(Br)[x := false]);
    ensures old(C.p)[x] != null ==> RefSetsEqual(Br, (old(Br)[x := false])[old(C.p)[x] := true]);
    // Framing conditions.
    ensures Frame_all(
        C.k, C.l, C.r, C.p, 
        C.min, C.max, C.keys,
        C.repr, C.black, C.black_height,
        old(C.k), old(C.l), old(C.r), old(C.p), 
        old(C.min), old(C.max), old(C.keys),
        old(C.repr), old(C.black), old(C.black_height),
        old(C.repr)[x], old(alloc)
    );

procedure RBTDeleteRightFixupContract(x: Ref) 
    returns (ret: Ref, fixed: bool);
    requires x != null;
    requires RefSetsDisjoint(Br, (C.repr[x])[x := false]);
    requires LC_Trans_DoubleBlack(C.k, C.l, C.r, C.p, 
                C.min, C.max, C.keys,
                C.repr, C.black, C.black_height, 
                x);
    requires (C.r[x] == null && C.l[x] != null && C.black_height[C.l[x]] == 1)
            || (C.r[x] != null && C.l[x] != null && C.black_height[C.l[x]] == C.black_height[C.r[x]] + 1);
    requires (C.r[x] == null || C.black[C.r[x]]);
    requires (C.black[x] || (C.l[x] == null || C.black[C.l[x]]));
    modifies Br, C.k, C.l, C.r, C.p, 
                C.min, C.max, C.keys,
                C.repr, C.black, C.black_height;
    ensures ret != null;
    ensures x != ret ==> (
        C.p[x] != null
        && C.p[x] != old(C.p)[x]
        && (C.repr[ret])[C.p[x]]
        && (C.l[x] != null ==> (C.repr[ret])[C.l[x]])
        && (C.r[x] != null ==> (C.repr[ret])[C.r[x]])
    );
    ensures LC(C.k, C.l, C.r, C.p, 
                C.min, C.max, C.keys,
                C.repr, C.black, C.black_height, 
                ret);
    ensures C.p[ret] == null;
    ensures KeySetsEqual(C.keys[ret], old(C.keys)[x]);
    ensures C.min[ret] == old(C.min)[x];
    ensures C.max[ret] == old(C.max)[x];
    ensures RefSetsEqual(C.repr[ret], old(C.repr)[x]);
    ensures C.black[ret] || (!C.black[ret] && !old(C.black)[x]);
    ensures (fixed && C.black_height[ret] == old(C.black_height)[x])
            ||  (!fixed && old(C.black)[x] && C.black_height[ret] == old(C.black_height)[x] - 1);
    ensures old(C.p)[x] == null ==> RefSetsEqual(Br, old(Br)[x := false]);
    ensures old(C.p)[x] != null ==> RefSetsEqual(Br, (old(Br)[x := false])[old(C.p)[x] := true]);
    // Framing conditions.
    ensures Frame_all(
        C.k, C.l, C.r, C.p, 
        C.min, C.max, C.keys,
        C.repr, C.black, C.black_height,
        old(C.k), old(C.l), old(C.r), old(C.p), 
        old(C.min), old(C.max), old(C.keys),
        old(C.repr), old(C.black), old(C.black_height),
        old(C.repr)[x], old(alloc)
    );

procedure RBTDeleteContract(x: Ref, k: int) 
    returns (ret: Ref, del: Ref, fixed: bool);
    requires x != null;
    requires RefSetsEqual(Br, EmptyRefSet);
    requires LC(C.k, C.l, C.r, C.p, 
                C.min, C.max, C.keys,
                C.repr, C.black, C.black_height, 
                x);
    modifies Br, C.k, C.l, C.r, C.p, 
                C.min, C.max, C.keys,
                C.repr, C.black, C.black_height;
    ensures x != ret && x != del ==> C.p[x] != old(C.p)[x];
    ensures ret != del;
    ensures !Br[x];
    ensures (ret == null ==>
                KeySetsEqual(old(C.keys)[x], EmptyKeySet[k := true])
                && RefSetsEqual(old(C.repr)[x], EmptyRefSet[x := true])
                && del != null
                && ((fixed && !old(C.black)[x]) || (!fixed && old(C.black)[x])));
    ensures (ret != null ==>
                LC(C.k, C.l, C.r, C.p, 
                    C.min, C.max, C.keys,
                    C.repr, C.black, C.black_height, ret)
                && (del != null ==> 
                        C.p[ret] == null
                        && KeySetsEqual(C.keys[ret], (old(C.keys)[x])[k := false])
                        && (k == old(C.min)[x] ==> C.min[ret] > old(C.min)[x])
                        && (k != old(C.min)[x] ==> C.min[ret] == old(C.min)[x])
                        && (k == old(C.max)[x] ==> C.max[ret] < old(C.max)[x])
                        && (k != old(C.max)[x] ==> C.max[ret] == old(C.max)[x])
                        && RefSetsEqual(C.repr[ret], (old(C.repr)[x])[del := false])
                        && (C.black[ret] || (!C.black[ret] && !old(C.black)[x]))
                        && ((C.black_height[ret] == old(C.black_height)[x] && fixed)
                            || (C.black_height[ret] == old(C.black_height)[x] - 1 && !fixed && old(C.black)[x])))
                && (del == null ==>
                        C.p[ret] == old(C.p)[x]
                        && KeySetsEqual(C.keys[ret], old(C.keys)[x])
                        && C.min[ret] == old(C.min)[x]
                        && C.max[ret] == old(C.max)[x]
                        && RefSetsEqual(C.repr[ret], old(C.repr)[x])
                        && C.black[ret] == old(C.black)[x]
                        && C.black_height[ret] == old(C.black_height)[x]));
    ensures del != null ==> (
        LC(C.k, C.l, C.r, C.p, 
            C.min, C.max, C.keys,
            C.repr, C.black, C.black_height, del)
        && Isolated(C.k, C.l, C.r, C.p, 
            C.min, C.max, C.keys,
            C.repr, C.black, C.black_height, del)
        && (old(C.keys)[x])[k]
        && (old(C.repr)[x])[del]
    );
    ensures del == null || old(C.p)[x] == null ==> RefSetsEqual(Br, EmptyRefSet);
    ensures del != null && old(C.p)[x] != null ==> RefSetsEqual(Br, EmptyRefSet[old(C.p)[x] := true]);
    // Framing conditions.
    ensures Frame_all(
        C.k, C.l, C.r, C.p, 
        C.min, C.max, C.keys,
        C.repr, C.black, C.black_height,
        old(C.k), old(C.l), old(C.r), old(C.p), 
        old(C.min), old(C.max), old(C.keys),
        old(C.repr), old(C.black), old(C.black_height),
        old(C.repr)[x], old(alloc)
    );

procedure RBTDelete(x: Ref, k: int) 
    returns (ret: Ref, del: Ref, fixed: bool)
    requires x != null;
    requires RefSetsEqual(Br, EmptyRefSet);
    requires LC(C.k, C.l, C.r, C.p, 
                C.min, C.max, C.keys,
                C.repr, C.black, C.black_height, 
                x);
    modifies Br, C.k, C.l, C.r, C.p, 
                C.min, C.max, C.keys,
                C.repr, C.black, C.black_height;
    ensures x != ret && x != del ==> C.p[x] != old(C.p)[x];
    ensures ret != del;
    ensures !Br[x];
    ensures (ret == null ==>
                KeySetsEqual(old(C.keys)[x], EmptyKeySet[k := true])
                && RefSetsEqual(old(C.repr)[x], EmptyRefSet[x := true])
                && del != null
                && ((fixed && !old(C.black)[x]) || (!fixed && old(C.black)[x])));
    ensures (ret != null ==>
                LC(C.k, C.l, C.r, C.p, 
                    C.min, C.max, C.keys,
                    C.repr, C.black, C.black_height, ret)
                && (del != null ==> 
                        C.p[ret] == null
                        && KeySetsEqual(C.keys[ret], (old(C.keys)[x])[k := false])
                        && (k == old(C.min)[x] ==> C.min[ret] > old(C.min)[x])
                        && (k != old(C.min)[x] ==> C.min[ret] == old(C.min)[x])
                        && (k == old(C.max)[x] ==> C.max[ret] < old(C.max)[x])
                        && (k != old(C.max)[x] ==> C.max[ret] == old(C.max)[x])
                        && RefSetsEqual(C.repr[ret], (old(C.repr)[x])[del := false])
                        && (C.black[ret] || (!C.black[ret] && !old(C.black)[x]))
                        && ((C.black_height[ret] == old(C.black_height)[x] && fixed)
                            || (C.black_height[ret] == old(C.black_height)[x] - 1 && !fixed && old(C.black)[x]))
                    )
                && (del == null ==>
                        C.p[ret] == old(C.p)[x]
                        && KeySetsEqual(C.keys[ret], old(C.keys)[x])
                        && C.min[ret] == old(C.min)[x]
                        && C.max[ret] == old(C.max)[x]
                        && RefSetsEqual(C.repr[ret], old(C.repr)[x])
                        && C.black[ret] == old(C.black)[x]
                        && C.black_height[ret] == old(C.black_height)[x])
                        );
    ensures del != null ==> (
        LC(C.k, C.l, C.r, C.p, 
            C.min, C.max, C.keys,
            C.repr, C.black, C.black_height, del)
        && Isolated(C.k, C.l, C.r, C.p, 
            C.min, C.max, C.keys,
            C.repr, C.black, C.black_height, del)
        && (old(C.keys)[x])[k]
        && (old(C.repr)[x])[del]
    );
    ensures del == null || old(C.p)[x] == null ==> RefSetsEqual(Br, EmptyRefSet);
    ensures del != null && old(C.p)[x] != null ==> RefSetsEqual(Br, EmptyRefSet[old(C.p)[x] := true]);
    // Framing conditions.
    ensures Frame_all(
        C.k, C.l, C.r, C.p, 
        C.min, C.max, C.keys,
        C.repr, C.black, C.black_height,
        old(C.k), old(C.l), old(C.r), old(C.p), 
        old(C.min), old(C.max), old(C.keys),
        old(C.repr), old(C.black), old(C.black_height),
        old(C.repr)[x], old(alloc)
    );
{
    // Local variables
    var xl: Ref;
    var xr: Ref;
    var min: int;
    var n: Ref;
    var minnode: Ref;
    var delnode: Ref;
    var oldl: Ref;
    var oldr: Ref;

    // Subexpressions
    var x_k: int; var x_black: bool;
    var xr_black_height: int;
    var xr_l: Ref; var xr_r: Ref;
    var xl_black_height: int;
    var xl_l: Ref; var xl_r: Ref;
    var x_l: Ref; var x_r: Ref;
    var x_l_min: int; var x_l_keys: KeySet; var x_l_repr: RefSet;
    var x_r_max: int; var x_r_keys: KeySet; var x_r_repr: RefSet;
    var x_black_height: int;

    call InAllocParam(x);

    call x_k := Get_k(x);
    if (k == x_k) {
        call xl := Get_l(x);
        call xr := Get_r(x);

        call IfNotBr_ThenLC(xl);
        call IfNotBr_ThenLC(xr);

        if (xl == null && xr == null) {
            call Set_p(x, null);
            call AssertLCAndRemove(x);
            call x_black := Get_black(x);
            fixed := !x_black;
            ret := null; del := x;
        } else if (xl == null) {
            call Set_p(x, null);
            call Set_l(x, null);
            call Set_r(x, null);
            call Set_p(xr, null);
            call x_k := Get_k(x);
            call Set_min(x, x_k);
            call Set_max(x, x_k);
            call Set_repr(x, EmptyRefSet[x := true]);
            call Set_keys(x, EmptyKeySet[x_k := true]);
            call xr_l := Get_l(xr);
            call xr_r := Get_r(xr);
            call IfNotBr_ThenLC(xr_l);
            call IfNotBr_ThenLC(xr_r);
            call Set_black(xr, true);
            call xr_black_height := Get_black_height(xr);
            call Set_black_height(xr, xr_black_height + 1);

            call AssertLCAndRemove(x);
            call AssertLCAndRemove(xr);

            fixed := true;
            ret := xr; del := x;
        } else if (xr == null) {
            call Set_p(x, null);
            call Set_l(x, null);
            call Set_r(x, null);
            call Set_p(xl, null);
            call x_k := Get_k(x);
            call Set_min(x, x_k);
            call Set_max(x, x_k);
            call Set_repr(x, EmptyRefSet[x := true]);
            call Set_keys(x, EmptyKeySet[x_k := true]);
            call xl_l := Get_l(xl);
            call xl_r := Get_r(xl);
            call IfNotBr_ThenLC(xl_l);
            call IfNotBr_ThenLC(xl_r);
            call Set_black(xl, true);
            call xl_black_height := Get_black_height(xl);
            call Set_black_height(xl, xl_black_height + 1);

            call AssertLCAndRemove(x);
            call AssertLCAndRemove(xl);

            fixed := true;
            ret := xl; del := x;
        } else {
            call min := RBTFindMinContract(xr);

            call n, minnode, fixed := RBTDeleteContract(xr, min);

            call IfNotBr_ThenLC(xr);
            
            if (minnode == null) {
                call IfNotBr_ThenLC(x);
                ret := x;
                del := null;
                fixed := true;
                return;
            }

            call Set_k(x, min);
            call Set_p(x, null);
            call Set_r(x, n);
            if (n != null) {
                call Set_p(n, x);
            }
            call AssertLCAndRemove(xr);

            call x_l := Get_l(x);
            call x_r := Get_r(x);
            call x_k := Get_k(x);
            call x_black := Get_black(x);
            call x_black_height := Get_black_height(x);
            if (x_l != null) {
                call x_l_min := Get_min(x_l);
                call x_l_keys := Get_keys(x_l);
                call x_l_repr := Get_repr(x_l);
            }
            if (x_r != null) {
                call x_r_max := Get_max(x_r);
                call x_r_keys := Get_keys(x_r);
                call x_r_repr := Get_repr(x_r);
            }
            call Set_min(x, if x_l == null then x_k else x_l_min);
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

            call AssertLCAndRemove(n);

            if (fixed) {
                call AssertLCAndRemove(x);

                ret := x; del := minnode;
                fixed := true;
            } else {
                call ret, fixed := RBTDeleteRightFixupContract(x);
                del := minnode;
            }
        }
    } else if (k < x_k) {
        call x_l := Get_l(x);
        call x_r := Get_r(x);
        call IfNotBr_ThenLC(x_l);
        call IfNotBr_ThenLC(x_r);

        if (x_l == null) {
            ret := x;
            del := null;
            fixed := true;
            return;
        }

        call n, delnode, fixed := RBTDeleteContract(x_l, k);

        call x_l := Get_l(x);
        if (x_l != null) {
            call IfNotBr_ThenLC(x_l);
        }

        if (delnode == null) {
            call IfNotBr_ThenLC(x);
            ret := x;
            del := null;
            fixed := true;
            return;
        }

        call Set_p(x, null);
        call oldl := Get_l(x);
        call Set_l(x, n);
        if (n != null) {
            call Set_p(n, x);
        }
        call AssertLCAndRemove(oldl);

        call x_l := Get_l(x);
        call x_r := Get_r(x);
        call x_k := Get_k(x);
        call x_black := Get_black(x);
        call x_black_height := Get_black_height(x);
        if (x_l != null) {
            call x_l_min := Get_min(x_l);
            call x_l_keys := Get_keys(x_l);
            call x_l_repr := Get_repr(x_l);
        }
        if (x_r != null) {
            call x_r_max := Get_max(x_r);
            call x_r_keys := Get_keys(x_r);
            call x_r_repr := Get_repr(x_r);
        }
        call Set_min(x, if x_l == null then x_k else x_l_min);
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

        call AssertLCAndRemove(n);

        if (fixed) {
            call AssertLCAndRemove(x);

            ret := x; del := delnode;
            fixed := true;
        } else {
            call ret, fixed := RBTDeleteLeftFixupContract(x);
            del := delnode;
        }
    } else {
        call x_l := Get_l(x);
        call x_r := Get_r(x);
        call IfNotBr_ThenLC(x_l);
        call IfNotBr_ThenLC(x_r);

        if (x_r == null) {
            ret := x;
            del := null;
            fixed := true;
            return;
        }

        call n, delnode, fixed := RBTDeleteContract(x_r, k);

        call x_r := Get_r(x);
        if (x_r != null) {
            call IfNotBr_ThenLC(x_r);
        }

        if (delnode == null) {
            call IfNotBr_ThenLC(x);
            ret := x;
            del := null;
            fixed := true;
            return;
        }

        call Set_p(x, null);
        call oldr := Get_r(x);
        call Set_r(x, n);
        if (n != null) {
            call Set_p(n, x);
        }
        call AssertLCAndRemove(oldr);

        call x_l := Get_l(x);
        call x_r := Get_r(x);
        call x_k := Get_k(x);
        call x_black := Get_black(x);
        call x_black_height := Get_black_height(x);
        if (x_l != null) {
            call x_l_min := Get_min(x_l);
            call x_l_keys := Get_keys(x_l);
            call x_l_repr := Get_repr(x_l);
        }
        if (x_r != null) {
            call x_r_max := Get_max(x_r);
            call x_r_keys := Get_keys(x_r);
            call x_r_repr := Get_repr(x_r);
        }
        call Set_min(x, if x_l == null then x_k else x_l_min);
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

        call AssertLCAndRemove(n);

        if (fixed) {
            call AssertLCAndRemove(x);

            ret := x; del := delnode;
            fixed := true;
        } else {
            call ret, fixed := RBTDeleteRightFixupContract(x);
            del := delnode;
        }
    }
}