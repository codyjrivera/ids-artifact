// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions of Datastructures"
// by Anonymous Authors.
// 
// Artifact by Anonymous Author, 2023. 
//
// Verification of Red-Black Tree Delete, right fixup procedure.

function {:inline} GetBlackHeight(black_height: [Ref]int, x: Ref) returns (int)
{
    if x == null then 0 else black_height[x]
}

function {:inline} MaxInt(x: int, y: int) returns (int)
{
    if x > y then x else y
}

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

procedure RBTDeleteRightFixup(x: Ref) 
    returns (ret: Ref, fixed: bool)
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
{
    // Local variable declarations
    var xl: Ref;
    var xr: Ref;
    var p: Ref;
    var xlr: Ref;
    var xll: Ref;
    var xlrl: Ref;
    var xlrr: Ref;
    var oldxblack: bool;
    var bh: int;
    var oldr: Ref;
    
    // Intermediate Expresssions
    var xl_r: Ref; var xl_black: bool;
    var x_l: Ref; var x_r: Ref;
    var x_k: int; var x_black: bool;
    var x_black_height: int; var x_l_min: int;
    var x_l_keys: KeySet; var x_l_repr: RefSet;
    var x_r_max: int; var x_r_keys: KeySet;
    var x_r_repr: RefSet; var xl_l: Ref;
    var xl_l_min: int;
    var xl_l_keys: KeySet; var xl_l_repr: RefSet;
    var xl_r_max: int; var xl_r_keys: KeySet;
    var xl_r_repr: RefSet; var xl_black_height: int;
    var xl_k: int; var xll_black: bool; var xlr_black: bool;
    var xll_black_height: int;
    var xlr_l: Ref; var xlr_r: Ref; var xlr_k: int;
    var xlr_l_min: int; var xlr_l_keys: KeySet; var xlr_l_repr: RefSet;
    var xlr_r_max: int; var xlr_r_keys: KeySet; var xlr_r_repr: RefSet;


    call InAllocParam(x);

    call xl := Get_l(x);
    call xr := Get_r(x);

    call IfNotBr_ThenLC(xl);
    call IfNotBr_ThenLC(xr);

    if (xl != null) {
        call xl_black := Get_black(xl);
    }
    if (xl != null && !xl_black) {
        call xlr := Get_r(xl);
        call xl_l := Get_l(xl);
        call IfNotBr_ThenLC(xlr);
        call IfNotBr_ThenLC(xl_l);

        call Set_l(x, xlr);
        if (xlr != null) {
            call Set_p(xlr, x);
        }
        call Set_r(xl, x);
        call Set_p(x, xl);
        call AssertLCAndRemove(xlr);

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
        if (x_black) {
            call Set_black_height(x, x_black_height - 1);
        }
        call Set_black(x, false);

        call p, fixed := RBTDeleteRightFixupContract(x);

        call IfNotBr_ThenLC(x);

        call oldr := Get_r(xl);
        call Set_r(xl, p);
        call Set_p(p, xl);
        call Set_p(xl, null);
        
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
        call Set_black(xl, true);
        call xl_black_height := Get_black_height(xl);
        call Set_black_height(xl, xl_black_height + 1);

        call AssertLCAndRemove(p);
        call AssertLCAndRemove(xl);
        call AssertLCAndRemove(oldr);
        
        ret := xl;
    } else {
        call xll := Get_l(xl);
        call xlr := Get_r(xl);

        call IfNotBr_ThenLC(xll);
        call IfNotBr_ThenLC(xlr);
        
        if (xlr != null) {
            call xlr_black := Get_black(xlr);
        }
        if (xll != null) {
            call xll_black := Get_black(xll);
        }
        if (xll != null && !xll_black) {
            fixed := true;
            call Set_l(x, xlr);
            if (xlr != null) {
                call Set_p(xlr, x);
            }
            call Set_r(xl, x);
            call Set_p(x, xl);
            call Set_p(xl, null);

            call oldxblack := Get_black(x);
            
            call xll_black_height := Get_black_height(xll);
            call Set_black_height(xll, xll_black_height + 1);
            call Set_black(xll, true);
            
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
            call Set_black(x, true);
            bh := MaxInt(GetBlackHeight(C.black_height, x_l), GetBlackHeight(C.black_height, x_r));
            call Set_black_height(x, bh + 1);

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
            call Set_black(xl, oldxblack);
            bh := MaxInt(GetBlackHeight(C.black_height, xl_l), GetBlackHeight(C.black_height, xl_r));
            call xl_black := Get_black(xl);
            if (xl_black) {
                call Set_black_height(xl, bh + 1);
            } else {
                call Set_black_height(xl, bh);
            }

            call AssertLCAndRemove(xlr);
            call AssertLCAndRemove(xll);
            call AssertLCAndRemove(x);
            call AssertLCAndRemove(xl);

            ret := xl;
        } else if (xlr == null || xlr_black) {
            call x_black := Get_black(x);
            fixed := !x_black;
            call xl_black := Get_black(xl);
            call xl_black_height := Get_black_height(xl);
            if (xl_black) {
                call Set_black_height(xl, xl_black_height - 1);
            }
            call Set_black(xl, false);
            call Set_black(x, true);
            call x_l := Get_l(x);
            call x_r := Get_r(x);
            bh := MaxInt(GetBlackHeight(C.black_height, x_l), GetBlackHeight(C.black_height, x_r));
            call Set_black_height(x, bh + 1);
            call Set_p(x, null);

            call AssertLCAndRemove(xl);
            call AssertLCAndRemove(x);

            ret := x;
        } else {
            fixed := true;
            call xlrl := Get_l(xlr);
            call xlrr := Get_r(xlr);
            
            call IfNotBr_ThenLC(xlrl);
            call IfNotBr_ThenLC(xlrr);

            call Set_r(xl, xlrl);
            if (xlrl != null) {
                call Set_p(xlrl, xl);
            }
            call Set_l(xlr, xl);
            call Set_p(xl, xlr);
            call Set_r(xlr, x);
            call Set_p(x, xlr);
            call Set_l(x, xlrr);
            if (xlrr != null) {
                call Set_p(xlrr, x);
            }
            call Set_p(xlr, null);

            call oldxblack := Get_black(x);

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
            call Set_black(x, true);
            bh := MaxInt(GetBlackHeight(C.black_height, x_l), GetBlackHeight(C.black_height, x_r));
            call Set_black_height(x, bh + 1);

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

            call xlr_l := Get_l(xlr);
            call xlr_r := Get_r(xlr);
            call xlr_k := Get_k(xlr);
            if (xlr_l != null) {
                call xlr_l_min := Get_min(xlr_l);
                call xlr_l_keys := Get_keys(xlr_l);
                call xlr_l_repr := Get_repr(xlr_l);
            }
            if (xlr_r != null) {
                call xlr_r_max := Get_max(xlr_r);
                call xlr_r_keys := Get_keys(xlr_r);
                call xlr_r_repr := Get_repr(xlr_r);
            }
            call Set_min(xlr, if xlr_l == null then xlr_k else xlr_l_min);
            call Set_max(xlr, if xlr_r == null then xlr_k else xlr_r_max);
            call Set_keys(xlr, 
                KeySetUnionF(
                    (if xlr_l == null then EmptyKeySet else xlr_l_keys)[xlr_k := true],
                    if xlr_r == null then EmptyKeySet else xlr_r_keys
                )
            );
            call Set_repr(xlr, 
                RefSetUnionF(
                    (if xlr_l == null then EmptyRefSet else xlr_l_repr)[xlr := true],
                    if xlr_r == null then EmptyRefSet else xlr_r_repr
                )
            ); 
            call Set_black(xlr, oldxblack);
            bh := MaxInt(GetBlackHeight(C.black_height, xlr_l), GetBlackHeight(C.black_height, xlr_r));
            call xlr_black := Get_black(xlr);
            if (xlr_black) {
                call Set_black_height(xlr, bh + 1);
            } else {
                call Set_black_height(xlr, bh);
            }

            call AssertLCAndRemove(xlrl);
            call AssertLCAndRemove(xlrr);
            call AssertLCAndRemove(x);
            call AssertLCAndRemove(xl);
            call AssertLCAndRemove(xlr);

            ret := xlr;
        }
    }
}
