// Supporting Artifact for
// "Predictive Verification using Intrinsic Definitions of Data Structures"
// by Adithya Murali, Cody Rivera, and P. Madhusudan.
// 
// Artifact by Cody Rivera, 2023. 
//
// Verification of Red-Black Tree Delete, left fixup procedure.

function {:inline} GetBlackHeight(black_height: [Ref]int, x: Ref) returns (int)
{
    if x == null then 0 else black_height[x]
}

function {:inline} MaxInt(x: int, y: int) returns (int)
{
    if x > y then x else y
}

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

// Local conditions
function {:inline} LC_Debug(
    k: [Ref]int, 
    l: [Ref]Ref,
    r: [Ref]Ref,
    p: [Ref]Ref,
    min: [Ref]int,
    max: [Ref]int,
    keys: [Ref]KeySet,
    repr: [Ref]RefSet,
    black: [Ref]bool,
    black_height: [Ref]int,
    x: Ref
) returns (bool)
{
    (x != null ==> (
        (repr[x])[x]
        && min[x] <= k[x] 
        && k[x] <= max[x]
        && (p[x] != null ==>
                !(repr[x])[p[x]]
                && (l[p[x]] == x || r[p[x]] == x))
        && (l[x] != null ==> 
                (repr[x])[l[x]]
                && !(repr[l[x]])[x]
                && p[l[x]] == x
                && max[l[x]] < k[x])
        && (r[x] != null ==> 
                (repr[x])[r[x]]
                && !(repr[r[x]])[x]
                && p[r[x]] == x
                && min[r[x]] > k[x])
        && (l[x] == null && r[x] == null ==>
                RefSetsEqual(repr[x], EmptyRefSet[x := true])
                && KeySetsEqual(keys[x], EmptyKeySet[k[x] := true])
                && min[x] == k[x] 
                && k[x] == max[x]
                )
        && (l[x] != null && r[x] == null ==>
                RefSetsEqual(repr[x], (repr[l[x]])[x := true])
                && KeySetsEqual(keys[x], (keys[l[x]])[k[x] := true])
                && !(keys[l[x]])[k[x]]
                && min[x] == min[l[x]] && max[x] == k[x]
                )
        && (l[x] == null && r[x] != null ==>
                RefSetsEqual(repr[x], (repr[r[x]])[x := true])
                && KeySetsEqual(keys[x], (keys[r[x]])[k[x] := true])
                && !(keys[r[x]])[k[x]]
                && min[x] == k[x] && max[x] == max[r[x]]
                )
        && (l[x] != null && r[x] != null ==>
                RefSetsEqual(repr[x], RefSetUnionF((repr[l[x]])[x := true], repr[r[x]]))
                && RefSetsDisjoint(repr[l[x]], repr[r[x]])
                && KeySetsEqual(keys[x], KeySetUnionF((keys[l[x]])[k[x] := true], keys[r[x]]))
                && KeySetsDisjoint(keys[l[x]], keys[r[x]])
                && !(keys[l[x]])[k[x]] && !(keys[r[x]])[k[x]]
                && min[x] == min[l[x]] && max[x] == max[r[x]]
                )
        // Special RBT properties
        && (l[x] == null && r[x] == null ==>
                black_height[x] == (if black[x] then 1 else 0))
        && (l[x] != null && r[x] == null ==>
                black_height[x] == (if black[x] then 1 else 0)
                && black_height[l[x]] == 0
                && (black[x] || black[l[x]])
                )
        && (l[x] == null && r[x] != null ==>
                black_height[x] == (if black[x] then 1 else 0)
                && black_height[r[x]] == 0
                && (black[x] || black[r[x]]))
        && (l[x] != null && r[x] != null ==>
                (black_height[l[x]] > black_height[r[x]] ==>
                    black_height[x] == (if black[x] then black_height[l[x]] + 1 else black_height[l[x]]))
                && (black_height[l[x]] <= black_height[r[x]] ==>
                        black_height[x] == (if black[x] then black_height[r[x]] + 1 else black_height[r[x]]))
                && black_height[l[x]] == black_height[r[x]]
                && (black[x] || (black[l[x]] && black[r[x]]))
            )
        && black_height[x] >= 0
    ))
}

procedure RBTDeleteLeftFixup(x: Ref) 
    returns (ret: Ref, fixed: bool)
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
{
    // Local variable declarations
    var xl: Ref;
    var xr: Ref;
    var p: Ref;
    var xrl: Ref;
    var xrr: Ref;
    var xrll: Ref;
    var xrlr: Ref;
    var oldxblack: bool;
    var bh: int;
    var oldl: Ref;
    
    // Intermediate Expresssions
    var xr_r: Ref; var xr_black: bool;
    var x_l: Ref; var x_r: Ref;
    var x_k: int; var x_black: bool;
    var x_black_height: int; var x_l_min: int;
    var x_l_keys: KeySet; var x_l_repr: RefSet;
    var x_r_max: int; var x_r_keys: KeySet;
    var x_r_repr: RefSet; var xr_l: Ref;
    var xr_l_min: int;
    var xr_l_keys: KeySet; var xr_l_repr: RefSet;
    var xr_r_max: int; var xr_r_keys: KeySet;
    var xr_r_repr: RefSet; var xr_black_height: int;
    var xr_k: int; var xrr_black: bool; var xrl_black: bool;
    var xrr_black_height: int;
    var xrl_l: Ref; var xrl_r: Ref; var xrl_k: int;
    var xrl_l_min: int; var xrl_l_keys: KeySet; var xrl_l_repr: RefSet;
    var xrl_r_max: int; var xrl_r_keys: KeySet; var xrl_r_repr: RefSet;


    call InAllocParam(x);

    call xl := Get_l(x);
    call xr := Get_r(x);

    call IfNotBr_ThenLC(xl);
    call IfNotBr_ThenLC(xr);

    if (xr != null) {
        call xr_black := Get_black(xr);
    }
    if (xr != null && !xr_black) {
        call xrl := Get_l(xr);
        call xr_r := Get_r(xr);
        call IfNotBr_ThenLC(xrl);
        call IfNotBr_ThenLC(xr_r);

        assert C.p[x] != null ==> !(C.repr[x])[C.p[x]];

        call Set_r(x, xrl);
        if (xrl != null) {
            call Set_p(xrl, x);
        }
        call Set_l(xr, x);
        call Set_p(x, xr);
        call AssertLCAndRemove(xrl);

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

        call p, fixed := RBTDeleteLeftFixupContract(x);

        call IfNotBr_ThenLC(x);

        call oldl := Get_l(xr);
        call Set_l(xr, p);
        call Set_p(p, xr);
        call Set_p(xr, null);
        
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
        call Set_black(xr, true);
        call xr_black_height := Get_black_height(xr);
        call Set_black_height(xr, xr_black_height + 1);

        call AssertLCAndRemove(p);
        call AssertLCAndRemove(xr);
        call AssertLCAndRemove(oldl);
        
        ret := xr;
    } else {
        call xrl := Get_l(xr);
        call xrr := Get_r(xr);

        call IfNotBr_ThenLC(xrl);
        call IfNotBr_ThenLC(xrr);
        
        if (xrr != null) {
            call xrr_black := Get_black(xrr);
        }
        if (xrl != null) {
            call xrl_black := Get_black(xrl);
        }
        if (xrr != null && !xrr_black) {
            fixed := true;
            call Set_r(x, xrl);
            if (xrl != null) {
                call Set_p(xrl, x);
            }
            call Set_l(xr, x);
            call Set_p(x, xr);
            call Set_p(xr, null);

            call oldxblack := Get_black(x);
            
            call xrr_black_height := Get_black_height(xrr);
            call Set_black_height(xrr, xrr_black_height + 1);
            call Set_black(xrr, true);
            
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
            call Set_black(xr, oldxblack);
            bh := MaxInt(GetBlackHeight(C.black_height, xr_l), GetBlackHeight(C.black_height, xr_r));
            call xr_black := Get_black(xr);
            if (xr_black) {
                call Set_black_height(xr, bh + 1);
            } else {
                call Set_black_height(xr, bh);
            }

            call AssertLCAndRemove(xrl);
            call AssertLCAndRemove(xrr);
            call AssertLCAndRemove(x);
            call AssertLCAndRemove(xr);

            ret := xr;
        } else if (xrl == null || xrl_black) {
            call x_black := Get_black(x);
            fixed := !x_black;
            call xr_black := Get_black(xr);
            call xr_black_height := Get_black_height(xr);
            if (xr_black) {
                call Set_black_height(xr, xr_black_height - 1);
            }
            call Set_black(xr, false);
            call Set_black(x, true);
            call x_l := Get_l(x);
            call x_r := Get_r(x);
            bh := MaxInt(GetBlackHeight(C.black_height, x_l), GetBlackHeight(C.black_height, x_r));
            call Set_black_height(x, bh + 1);
            call Set_p(x, null);

            call AssertLCAndRemove(xr);
            call AssertLCAndRemove(x);

            ret := x;
        } else {
            fixed := true;
            call xrll := Get_l(xrl);
            call xrlr := Get_r(xrl);
            
            call IfNotBr_ThenLC(xrll);
            call IfNotBr_ThenLC(xrlr);

            call Set_l(xr, xrlr);
            if (xrlr != null) {
                call Set_p(xrlr, xr);
            }
            call Set_r(xrl, xr);
            call Set_p(xr, xrl);
            call Set_l(xrl, x);
            call Set_p(x, xrl);
            call Set_r(x, xrll);
            if (xrll != null) {
                call Set_p(xrll, x);
            }
            call Set_p(xrl, null);

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

            call xrl_l := Get_l(xrl);
            call xrl_r := Get_r(xrl);
            call xrl_k := Get_k(xrl);
            if (xrl_l != null) {
                call xrl_l_min := Get_min(xrl_l);
                call xrl_l_keys := Get_keys(xrl_l);
                call xrl_l_repr := Get_repr(xrl_l);
            }
            if (xrl_r != null) {
                call xrl_r_max := Get_max(xrl_r);
                call xrl_r_keys := Get_keys(xrl_r);
                call xrl_r_repr := Get_repr(xrl_r);
            }
            call Set_min(xrl, if xrl_l == null then xrl_k else xrl_l_min);
            call Set_max(xrl, if xrl_r == null then xrl_k else xrl_r_max);
            call Set_keys(xrl, 
                KeySetUnionF(
                    (if xrl_l == null then EmptyKeySet else xrl_l_keys)[xrl_k := true],
                    if xrl_r == null then EmptyKeySet else xrl_r_keys
                )
            );
            call Set_repr(xrl, 
                RefSetUnionF(
                    (if xrl_l == null then EmptyRefSet else xrl_l_repr)[xrl := true],
                    if xrl_r == null then EmptyRefSet else xrl_r_repr
                )
            ); 
            call Set_black(xrl, oldxblack);
            bh := MaxInt(GetBlackHeight(C.black_height, xrl_l), GetBlackHeight(C.black_height, xrl_r));
            call xrl_black := Get_black(xrl);
            if (xrl_black) {
                call Set_black_height(xrl, bh + 1);
            } else {
                call Set_black_height(xrl, bh);
            }

            call AssertLCAndRemove(xrll);
            call AssertLCAndRemove(xrlr);
            call AssertLCAndRemove(x);
            call AssertLCAndRemove(xr);
            call AssertLCAndRemove(xrl);

            ret := xrl;
        }
    }
}
