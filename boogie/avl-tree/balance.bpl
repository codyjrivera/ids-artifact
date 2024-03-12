// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions"
// by Anonymous Authors.
// 
// Artifact by Anonymous Author, 2023. 
//
// Verification of AVL Balance.

function {:inline} GetHeight(height: [Ref]int, x: Ref) returns (int)
{
    if x == null then 0 else height[x]
}

procedure AVLBalance(x: Ref) returns (ret: Ref)
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
{
    // Local variables
    var xl: Ref;
    var xr: Ref;
    var diff: int;
    var rl: Ref;
    var rr: Ref;
    var rrht: int;
    var rlht: int;
    var rll: Ref;
    var rlr: Ref;
    var lht: int;
    var ll: Ref;
    var lr: Ref;
    var llht: int;
    var lrht: int;
    var lrl: Ref;
    var lrr: Ref;
    var rht: int;


    // Subexpressions
    var x_l: Ref; var x_r: Ref; var x_k: int; 
    var x_l_min: int; var x_r_max: int; 
    var x_l_keys: KeySet; var x_l_repr: RefSet;
    var x_r_keys: KeySet; var x_r_repr: RefSet;
    var xr_l: Ref; var xr_r: Ref; var xr_k: int; 
    var xr_l_min: int; var xr_r_max: int; 
    var xr_l_keys: KeySet; var xr_l_repr: RefSet;
    var xr_r_keys: KeySet; var xr_r_repr: RefSet;
    var rl_l: Ref; var rl_r: Ref; var rl_k: int; 
    var rl_l_min: int; var rl_r_max: int; 
    var rl_l_keys: KeySet; var rl_l_repr: RefSet;
    var rl_r_keys: KeySet; var rl_r_repr: RefSet;
    var xl_l: Ref; var xl_r: Ref; var xl_k: int; 
    var xl_l_min: int; var xl_r_max: int; 
    var xl_l_keys: KeySet; var xl_l_repr: RefSet;
    var xl_r_keys: KeySet; var xl_r_repr: RefSet;
    var lr_l: Ref; var lr_r: Ref; var lr_k: int; 
    var lr_l_min: int; var lr_r_max: int; 
    var lr_l_keys: KeySet; var lr_l_repr: RefSet;
    var lr_r_keys: KeySet; var lr_r_repr: RefSet;

    call InAllocParam(x);
    call xl := Get_l(x);
    call xr := Get_r(x);

    call IfNotBr_ThenLC(xl);
    call IfNotBr_ThenLC(xr);

    diff := GetHeight(C.height, xr) - GetHeight(C.height, xl);

    if (-1 <= diff && diff <= 1) {
        call Set_p(x, null);
        call AssertLCAndRemove(x);
        ret := x;
        return;
    }

    if (diff == 2) {
        call rl := Get_l(xr);
        call rr := Get_r(xr);

        call IfNotBr_ThenLC(rl);
        call IfNotBr_ThenLC(rr);

        rlht := GetHeight(C.height, rl);
        rrht := GetHeight(C.height, rr);

        if (rlht <= rrht) {
            call Set_r(x, rl);
            if (rl != null) {
                call Set_p(rl, x);
            }
            call Set_height(x, rlht + 1);

            call Set_l(xr, x);
            call Set_p(x, xr);
            call Set_height(xr, rlht + 2);
            call Set_p(xr, null);

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

            call xr_l := Get_l(xr);
            call xr_r := Get_r(xr);
            call xr_k := Get_k(xr);
            if (xr_l != null) {
                call xr_l_min := Get_min(xr_l);
                call xr_l_keys := Get_keys(xr_l);
                call xr_l_repr := Get_repr(xr_l);
            }
            if (xr_r != null) {
                call xr_r_max := Get_max(xr_r);
                call xr_r_keys := Get_keys(xr_r);
                call xr_r_repr := Get_repr(xr_r);
            }
            call Set_min(xr, if xr_l == null then xr_k else xr_l_min);
            call Set_max(xr, if xr_r == null then xr_k else xr_r_max);
            call Set_keys(xr, 
                KeySetUnionF(
                    (if xr_l == null then EmptyKeySet else xr_l_keys)[xr_k := true],
                    if xr_r == null then EmptyKeySet else xr_r_keys
                )
            );
            call Set_repr(xr, 
                RefSetUnionF(
                    (if xr_l == null then EmptyRefSet else xr_l_repr)[xr := true],
                    if xr_r == null then EmptyRefSet else xr_r_repr
                )
            ); 

            call AssertLCAndRemove(rl);
            call AssertLCAndRemove(x);
            call AssertLCAndRemove(xr);

            ret := xr;
        } else {
            call rll := Get_l(rl);
            call rlr := Get_r(rl);

            call IfNotBr_ThenLC(rll);
            call IfNotBr_ThenLC(rlr);
            
            lht := GetHeight(C.height, xl);

            call Set_r(x, rll);
            if (rll != null) {
                call Set_p(rll, x);
            }
            call Set_height(x, lht + 1);

            call Set_l(xr, rlr);
            if (rlr != null) {
                call Set_p(rlr, xr);
            }
            call Set_height(xr, rrht + 1);

            call Set_l(rl, x);
            call Set_p(x, rl);
            call Set_r(rl, xr);
            call Set_p(xr, rl);
            call Set_height(rl, lht + 2);
            call Set_p(rl, null);

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

            call xr_l := Get_l(xr);
            call xr_r := Get_r(xr);
            call xr_k := Get_k(xr);
            if (xr_l != null) {
                call xr_l_min := Get_min(xr_l);
                call xr_l_keys := Get_keys(xr_l);
                call xr_l_repr := Get_repr(xr_l);
            }
            if (xr_r != null) {
                call xr_r_max := Get_max(xr_r);
                call xr_r_keys := Get_keys(xr_r);
                call xr_r_repr := Get_repr(xr_r);
            }
            call Set_min(xr, if xr_l == null then xr_k else xr_l_min);
            call Set_max(xr, if xr_r == null then xr_k else xr_r_max);
            call Set_keys(xr, 
                KeySetUnionF(
                    (if xr_l == null then EmptyKeySet else xr_l_keys)[xr_k := true],
                    if xr_r == null then EmptyKeySet else xr_r_keys
                )
            );
            call Set_repr(xr, 
                RefSetUnionF(
                    (if xr_l == null then EmptyRefSet else xr_l_repr)[xr := true],
                    if xr_r == null then EmptyRefSet else xr_r_repr
                )
            ); 

            call rl_l := Get_l(rl);
            call rl_r := Get_r(rl);
            call rl_k := Get_k(rl);
            if (rl_l != null) {
                call rl_l_min := Get_min(rl_l);
                call rl_l_keys := Get_keys(rl_l);
                call rl_l_repr := Get_repr(rl_l);
            }
            if (rl_r != null) {
                call rl_r_max := Get_max(rl_r);
                call rl_r_keys := Get_keys(rl_r);
                call rl_r_repr := Get_repr(rl_r);
            }
            call Set_min(rl, if rl_l == null then rl_k else rl_l_min);
            call Set_max(rl, if rl_r == null then rl_k else rl_r_max);
            call Set_keys(rl, 
                KeySetUnionF(
                    (if rl_l == null then EmptyKeySet else rl_l_keys)[rl_k := true],
                    if rl_r == null then EmptyKeySet else rl_r_keys
                )
            );
            call Set_repr(rl, 
                RefSetUnionF(
                    (if rl_l == null then EmptyRefSet else rl_l_repr)[rl := true],
                    if rl_r == null then EmptyRefSet else rl_r_repr
                )
            );

            call AssertLCAndRemove(rll);
            call AssertLCAndRemove(rlr);
            call AssertLCAndRemove(x);
            call AssertLCAndRemove(xr);
            call AssertLCAndRemove(rl);

            ret := rl;
        }
    } else {
        call lr := Get_r(xl);
        call ll := Get_l(xl);

        call IfNotBr_ThenLC(lr);
        call IfNotBr_ThenLC(ll);

        lrht := GetHeight(C.height, lr);
        llht := GetHeight(C.height, ll);

        if (lrht <= llht) {
            call Set_l(x, lr);
            if (lr != null) {
                call Set_p(lr, x);
            }
            call Set_height(x, lrht + 1);

            call Set_r(xl, x);
            call Set_p(x, xl);
            call Set_height(xl, lrht + 2);
            call Set_p(xl, null);

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

            call xl_l := Get_l(xl);
            call xl_r := Get_r(xl);
            call xl_k := Get_k(xl);
            if (xl_l != null) {
                call xl_l_min := Get_min(xl_l);
                call xl_l_keys := Get_keys(xl_l);
                call xl_l_repr := Get_repr(xl_l);
            }
            if (xl_r != null) {
                call xl_r_max := Get_max(xl_r);
                call xl_r_keys := Get_keys(xl_r);
                call xl_r_repr := Get_repr(xl_r);
            }
            call Set_min(xl, if xl_l == null then xl_k else xl_l_min);
            call Set_max(xl, if xl_r == null then xl_k else xl_r_max);
            call Set_keys(xl, 
                KeySetUnionF(
                    (if xl_l == null then EmptyKeySet else xl_l_keys)[xl_k := true],
                    if xl_r == null then EmptyKeySet else xl_r_keys
                )
            );
            call Set_repr(xl, 
                RefSetUnionF(
                    (if xl_l == null then EmptyRefSet else xl_l_repr)[xl := true],
                    if xl_r == null then EmptyRefSet else xl_r_repr
                )
            ); 

            call AssertLCAndRemove(lr);
            call AssertLCAndRemove(x);
            call AssertLCAndRemove(xl);

            ret := xl;
        } else {
            call lrl := Get_l(lr);
            call lrr := Get_r(lr);

            call IfNotBr_ThenLC(lrl);
            call IfNotBr_ThenLC(lrr);
            
            rht := GetHeight(C.height, xr);

            call Set_l(x, lrr);
            if (lrr != null) {
                call Set_p(lrr, x);
            }
            call Set_height(x, rht + 1);

            call Set_r(xl, lrl);
            if (lrl != null) {
                call Set_p(lrl, xl);
            }
            call Set_height(xl, llht + 1);

            call Set_r(lr, x);
            call Set_p(x, lr);
            call Set_l(lr, xl);
            call Set_p(xl, lr);
            call Set_height(lr, rht + 2);
            call Set_p(lr, null);

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

            call xl_l := Get_l(xl);
            call xl_r := Get_r(xl);
            call xl_k := Get_k(xl);
            if (xl_l != null) {
                call xl_l_min := Get_min(xl_l);
                call xl_l_keys := Get_keys(xl_l);
                call xl_l_repr := Get_repr(xl_l);
            }
            if (xl_r != null) {
                call xl_r_max := Get_max(xl_r);
                call xl_r_keys := Get_keys(xl_r);
                call xl_r_repr := Get_repr(xl_r);
            }
            call Set_min(xl, if xl_l == null then xl_k else xl_l_min);
            call Set_max(xl, if xl_r == null then xl_k else xl_r_max);
            call Set_keys(xl, 
                KeySetUnionF(
                    (if xl_l == null then EmptyKeySet else xl_l_keys)[xl_k := true],
                    if xl_r == null then EmptyKeySet else xl_r_keys
                )
            );
            call Set_repr(xl, 
                RefSetUnionF(
                    (if xl_l == null then EmptyRefSet else xl_l_repr)[xl := true],
                    if xl_r == null then EmptyRefSet else xl_r_repr
                )
            ); 

            call lr_l := Get_l(lr);
            call lr_r := Get_r(lr);
            call lr_k := Get_k(lr);
            if (lr_l != null) {
                call lr_l_min := Get_min(lr_l);
                call lr_l_keys := Get_keys(lr_l);
                call lr_l_repr := Get_repr(lr_l);
            }
            if (lr_r != null) {
                call lr_r_max := Get_max(lr_r);
                call lr_r_keys := Get_keys(lr_r);
                call lr_r_repr := Get_repr(lr_r);
            }
            call Set_min(lr, if lr_l == null then lr_k else lr_l_min);
            call Set_max(lr, if lr_r == null then lr_k else lr_r_max);
            call Set_keys(lr, 
                KeySetUnionF(
                    (if lr_l == null then EmptyKeySet else lr_l_keys)[lr_k := true],
                    if lr_r == null then EmptyKeySet else lr_r_keys
                )
            );
            call Set_repr(lr, 
                RefSetUnionF(
                    (if lr_l == null then EmptyRefSet else lr_l_repr)[lr := true],
                    if lr_r == null then EmptyRefSet else lr_r_repr
                )
            );

            call AssertLCAndRemove(lrl);
            call AssertLCAndRemove(lrr);
            call AssertLCAndRemove(x);
            call AssertLCAndRemove(xl);
            call AssertLCAndRemove(lr);

            ret := lr;
        }
    }
}
    