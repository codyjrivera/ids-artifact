// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions"
// by Adithya Murali, Cody Rivera, and P. Madhusudan.
// 
// Artifact by Cody Rivera, 2023. 
//
// Verification of AVL Delete.

function {:inline} GetHeight(height: [Ref]int, x: Ref) returns (int)
{
    if x == null then 0 else height[x]
}

function {:inline} MaxInt(x: int, y: int) returns (int)
{
    if x > y then x else y
}

procedure AVLFindMinContract(x: Ref) returns (ret: int);
    requires x != null;
    requires RefSetsDisjoint(Br, C.repr[x]);
    requires LC(C.k, C.l, C.r, C.p, C.height, 
                C.min, C.max, C.keys, C.repr,
                x);
    ensures (C.keys[x])[ret];
    ensures ret == C.min[x];

procedure AVLBalanceContract(x: Ref) returns (ret: Ref);
    requires x != null;
    requires RefSetsDisjoint(Br, (C.repr[x])[x := false]);
    requires LC_Trans_Unbalanced(C.k, C.l, C.r, C.p, C.height, 
                                    C.min, C.max, C.keys, C.repr,
                                    x);
    modifies Br, C.k, C.l, C.r, C.p, C.height, 
                C.min, C.max, C.keys, C.repr;
    ensures ret != null;
    ensures x != ret ==> (
        C.p[x] != null
        && C.p[x] != old(C.p)[x]
        && (C.repr[ret])[C.p[x]]
        && (C.l[x] != null ==> (C.repr[ret])[C.l[x]])
        && (C.r[x] != null ==> (C.repr[ret])[C.r[x]])
    );
    ensures LC(C.k, C.l, C.r, C.p, C.height, 
                C.min, C.max, C.keys, C.repr,
                ret);
    ensures C.p[ret] == null;
    ensures KeySetsEqual(C.keys[ret], old(C.keys)[x]);
    ensures RefSetsEqual(C.repr[ret], old(C.repr)[x]);
    ensures C.min[ret] == old(C.min)[x];
    ensures C.max[ret] == old(C.max)[x];
    ensures (C.height[ret] == old(C.height)[x] || C.height[ret] == old(C.height)[x] - 1);
    ensures (
        (-1 <= GetHeight(old(C.height), old(C.r)[x]) - GetHeight(old(C.height), old(C.l)[x])
        && GetHeight(old(C.height), old(C.r)[x]) - GetHeight(old(C.height), old(C.l)[x]) <= 1)
        ==>
        C.height[ret] == old(C.height)[x]
    );
    ensures old(C.p)[x] == null ==> RefSetsEqual(Br, old(Br)[x := false]);
    ensures old(C.p)[x] != null ==> RefSetsEqual(Br, (old(Br)[x := false])[old(C.p)[x] := true]);
    // Framing conditions.
    ensures Frame_all(
        C.k, C.l, C.r, C.p, C.height,
        C.min, C.max, C.keys, C.repr,
        old(C.k), old(C.l), old(C.r), old(C.p), old(C.height), 
        old(C.min), old(C.max), old(C.keys), old(C.repr),
        old(C.repr)[x], old(alloc)
    );

procedure AVLDeleteContract(x: Ref, k: int) 
    returns (ret: Ref, del: Ref);
    requires x != null;
    requires RefSetsEqual(Br, EmptyRefSet);
    requires LC(C.k, C.l, C.r, C.p, C.height, 
                C.min, C.max, C.keys, C.repr,
                x);
    modifies Br, C.k, C.l, C.r, C.p, C.height,
                C.min, C.max, C.keys, C.repr;
    ensures x != ret && x != del ==> C.p[x] != old(C.p)[x];
    ensures ret != del;
    ensures !Br[x];
    ensures (ret == null ==>
                KeySetsEqual(old(C.keys)[x], EmptyKeySet[k := true])
                && RefSetsEqual(old(C.repr)[x], EmptyRefSet[x := true])
                && del != null);
    ensures (ret != null ==>
                LC(C.k, C.l, C.r, C.p, C.height, 
                    C.min, C.max, C.keys, C.repr,
                    ret)
                && (del != null ==> 
                        C.p[ret] == null
                        && KeySetsEqual(C.keys[ret], (old(C.keys)[x])[k := false])
                        && (k == old(C.min)[x] ==> C.min[ret] > old(C.min)[x])
                        && (k != old(C.min)[x] ==> C.min[ret] == old(C.min)[x])
                        && (k == old(C.max)[x] ==> C.max[ret] < old(C.max)[x])
                        && (k != old(C.max)[x] ==> C.max[ret] == old(C.max)[x])
                        && RefSetsEqual(C.repr[ret], (old(C.repr)[x])[del := false])
                        && (C.height[ret] == old(C.height)[x] || C.height[ret] == old(C.height)[x] - 1))
                && (del == null ==>
                        C.p[ret] == old(C.p)[x]
                        && KeySetsEqual(C.keys[ret], old(C.keys)[x])
                        && C.min[ret] == old(C.min)[x]
                        && C.max[ret] == old(C.max)[x]
                        && RefSetsEqual(C.repr[ret], old(C.repr)[x])
                        && C.height[ret] == old(C.height)[x]));
    ensures del != null ==> (
        LC(C.k, C.l, C.r, C.p, C.height, 
            C.min, C.max, C.keys, C.repr,
            del)
        && Isolated(C.k, C.l, C.r, C.p, C.height,
            C.min, C.max, C.keys, C.repr,
            del)
        && (old(C.keys)[x])[k]
        && (old(C.repr)[x])[del]
    );
    ensures del == null || old(C.p)[x] == null ==> RefSetsEqual(Br, EmptyRefSet);
    ensures del != null && old(C.p)[x] != null ==> RefSetsEqual(Br, EmptyRefSet[old(C.p)[x] := true]);
    // Framing conditions.
    ensures Frame_all(
        C.k, C.l, C.r, C.p, C.height,
        C.min, C.max, C.keys, C.repr,
        old(C.k), old(C.l), old(C.r), old(C.p), old(C.height),
        old(C.min), old(C.max), old(C.keys), old(C.repr),
        old(C.repr)[x], old(alloc)
    );

procedure AVLDelete(x: Ref, k: int) 
    returns (ret: Ref, del: Ref)
    requires x != null;
    requires RefSetsEqual(Br, EmptyRefSet);
    requires LC(C.k, C.l, C.r, C.p, C.height, 
                C.min, C.max, C.keys, C.repr,
                x);
    modifies Br, C.k, C.l, C.r, C.p, C.height,
                C.min, C.max, C.keys, C.repr;
    ensures x != ret && x != del ==> C.p[x] != old(C.p)[x];
    ensures ret != del;
    ensures !Br[x];
    ensures (ret == null ==>
                KeySetsEqual(old(C.keys)[x], EmptyKeySet[k := true])
                && RefSetsEqual(old(C.repr)[x], EmptyRefSet[x := true])
                && del != null);
    ensures (ret != null ==>
                LC(C.k, C.l, C.r, C.p, C.height, 
                    C.min, C.max, C.keys, C.repr,
                    ret)
                && (del != null ==> 
                        C.p[ret] == null
                        && KeySetsEqual(C.keys[ret], (old(C.keys)[x])[k := false])
                        && (k == old(C.min)[x] ==> C.min[ret] > old(C.min)[x])
                        && (k != old(C.min)[x] ==> C.min[ret] == old(C.min)[x])
                        && (k == old(C.max)[x] ==> C.max[ret] < old(C.max)[x])
                        && (k != old(C.max)[x] ==> C.max[ret] == old(C.max)[x])
                        && RefSetsEqual(C.repr[ret], (old(C.repr)[x])[del := false])
                        && (C.height[ret] == old(C.height)[x] || C.height[ret] == old(C.height)[x] - 1))
                && (del == null ==>
                        C.p[ret] == old(C.p)[x]
                        && KeySetsEqual(C.keys[ret], old(C.keys)[x])
                        && C.min[ret] == old(C.min)[x]
                        && C.max[ret] == old(C.max)[x]
                        && RefSetsEqual(C.repr[ret], old(C.repr)[x])
                        && C.height[ret] == old(C.height)[x]));
    ensures del != null ==> (
        LC(C.k, C.l, C.r, C.p, C.height, 
            C.min, C.max, C.keys, C.repr,
            del)
        && Isolated(C.k, C.l, C.r, C.p, C.height,
            C.min, C.max, C.keys, C.repr,
            del)
        && (old(C.keys)[x])[k]
        && (old(C.repr)[x])[del]
    );
    ensures del == null || old(C.p)[x] == null ==> RefSetsEqual(Br, EmptyRefSet);
    ensures del != null && old(C.p)[x] != null ==> RefSetsEqual(Br, EmptyRefSet[old(C.p)[x] := true]);
    // Framing conditions.
    ensures Frame_all(
        C.k, C.l, C.r, C.p, C.height,
        C.min, C.max, C.keys, C.repr,
        old(C.k), old(C.l), old(C.r), old(C.p), old(C.height),
        old(C.min), old(C.max), old(C.keys), old(C.repr),
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
    var x_k: int; var x_l: Ref; var x_r: Ref;
    var x_l_min: int; var x_r_max: int; 
    var x_l_keys: KeySet; var x_l_repr: RefSet;
    var x_r_keys: KeySet; var x_r_repr: RefSet;

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
            ret := null; del := x;
        } else if (xl == null) {
            call Set_p(x, null);
            call Set_l(x, null);
            call Set_r(x, null);
            call Set_p(xr, null);
            call Set_min(x, x_k);
            call Set_max(x, x_k);
            call Set_repr(x, EmptyRefSet[x := true]);
            call Set_keys(x, EmptyKeySet[x_k := true]);
            call Set_height(x, 1);

            call AssertLCAndRemove(x);
            call AssertLCAndRemove(xr);

            ret := xr; del := x;
        } else if (xr == null) {
            call Set_p(x, null);
            call Set_l(x, null);
            call Set_r(x, null);
            call Set_p(xl, null);
            call Set_min(x, x_k);
            call Set_max(x, x_k);
            call Set_repr(x, EmptyRefSet[x := true]);
            call Set_keys(x, EmptyKeySet[x_k := true]);
            call Set_height(x, 1);

            call AssertLCAndRemove(x);
            call AssertLCAndRemove(xl);

            ret := xl; del := x;
        } else {
            call min := AVLFindMinContract(xr);

            call n, minnode := AVLDeleteContract(xr, min);

            call IfNotBr_ThenLC(xr);
            
            if (minnode == null) {
                call IfNotBr_ThenLC(x);
                ret := x;
                del := null;
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
            call Set_height(x, MaxInt(GetHeight(C.height, x_l), GetHeight(C.height, x_r)) + 1);

            call AssertLCAndRemove(n);

            call ret := AVLBalanceContract(x);
            del := minnode;
        }
    } else if (k < x_k) {
        call x_l := Get_l(x);
        call x_r := Get_r(x);
        call IfNotBr_ThenLC(x_l);
        call IfNotBr_ThenLC(x_r);

        if (x_l == null) {
            ret := x;
            del := null;
            return;
        }

        call n, delnode := AVLDeleteContract(x_l, k);

        call x_l := Get_l(x);
        if (x_l != null) {
            call IfNotBr_ThenLC(x_l);
        }

        if (delnode == null) {
            call IfNotBr_ThenLC(x);
            ret := x;
            del := null;
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
        call Set_height(x, MaxInt(GetHeight(C.height, x_l), GetHeight(C.height, x_r)) + 1);

        call AssertLCAndRemove(n);

        call ret := AVLBalanceContract(x);
        del := delnode;
    } else {
        call x_l := Get_l(x);
        call x_r := Get_r(x);
        call IfNotBr_ThenLC(x_l);
        call IfNotBr_ThenLC(x_r);

        if (x_r == null) {
            ret := x;
            del := null;
            return;
        }

        call n, delnode := AVLDeleteContract(x_r, k);

        call x_r := Get_r(x);
        if (x_r != null) {
            call IfNotBr_ThenLC(x_r);
        }

        if (delnode == null) {
            call IfNotBr_ThenLC(x);
            ret := x;
            del := null;
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
        call Set_height(x, MaxInt(GetHeight(C.height, x_l), GetHeight(C.height, x_r)) + 1);

        call AssertLCAndRemove(n);

        call ret := AVLBalanceContract(x);
        del := delnode;
    }
}