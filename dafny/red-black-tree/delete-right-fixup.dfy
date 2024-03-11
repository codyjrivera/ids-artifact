// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions"
// by Anonymous Authors.
// 
// Artifact by Anonymous Author, 2023-2024. 
//
// Verification of RBT Right Fixup.

include "red-black-tree.dfy"

ghost function GetBlackHeight(x: RBTNode?): nat
    reads x
{
    if x == null then 0 else x.black_height
}

ghost function MaxNat(x: nat, y: nat): nat {
    if x > y then x else y
}

/**
 * RBT right fixup.
 */
method RBTDeleteRightFixup(ghost Br: set<RBTNode>, x: RBTNode)
    returns (ghost Br': set<RBTNode>, ret: RBTNode, fixed: bool)
    requires Br !! (x.repr - {x})
    requires x.LC_Trans_DoubleBlack()
    requires (x.r == null && x.l != null && x.l.black_height == 1)
            || (x.r != null && x.l != null && x.l.black_height == x.r.black_height + 1)
    requires (x.r == null || x.r.black)
    requires (x.black || (x.l == null || x.l.black))
    modifies x.repr
    decreases x.repr
    ensures x != ret ==> 
                x.p != old(x.p) 
                && x.p in ret.repr 
                && (x.l != null ==> x.l in ret.repr)
                && (x.r != null ==> x.r in ret.repr)
    ensures ret.LC()
    ensures ret.p == null
            && ret.keys == old(x.keys)
            && ret.min == old(x.min)
            && ret.max == old(x.max)
            && ret.repr == old(x.repr)
    ensures ret.black || (!ret.black && !old(x.black))
    ensures (fixed && ret.black_height == old(x.black_height))
            ||  (!fixed && old(x.black) && ret.black_height == old(x.black_height) - 1)
    ensures old(x.p) == null ==> Br' == Br - {x} 
    ensures old(x.p) != null ==> Br' == (Br - {x}) + {old(x.p)}
{
    Br' := Br;
    var xl := x.l;
    var xr := x.r;

    if xl != null {
        IfNotBr_ThenLC(Br', x.l);
    }
    if xr != null {
        IfNotBr_ThenLC(Br', x.r);
    }

    if xl != null && !xl.black {
        var xlr := xl.r;
        if xlr != null {
            IfNotBr_ThenLC(Br', xlr);
        }
        if xl.l != null {
            IfNotBr_ThenLC(Br', xl.l);
        }
        Br' := x.Set_l(Br', xlr);
        if xlr != null {
            Br' := xlr.Set_p(Br', x);
        }
        Br' := xl.Set_r(Br', x);
        Br' := x.Set_p(Br', xl);

        Br' := AssertLCAndRemove(Br', xlr);
        Br' := x.Set_min(Br', if x.l == null then x.k else x.l.min);
        Br' := x.Set_max(Br', if x.r == null then x.k else x.r.max);
        Br' := x.Set_keys(Br', (if x.l == null then {} else x.l.keys) 
                                    + {x.k} + (if x.r == null then {} else x.r.keys));
        Br' := x.Set_repr(Br', (if x.l == null then {} else x.l.repr) 
                                    + {x} + (if x.r == null then {} else x.r.repr));
        if x.black {
            Br' := x.Set_black_height(Br', x.black_height - 1);
        }
        Br' := x.Set_black(Br', false);

        var p;
        Br', p, fixed := RBTDeleteRightFixup(Br', x);

        IfNotBr_ThenLC(Br', x);

        ghost var oldr := xl.r;
        Br' := xl.Set_r(Br', p);
        Br' := p.Set_p(Br', xl);
        Br' := xl.Set_p(Br', null);

        Br' := xl.Set_min(Br', if xl.l == null then xl.k else xl.l.min);
        Br' := xl.Set_max(Br', if xl.r == null then xl.k else xl.r.max);
        Br' := xl.Set_keys(Br', (if xl.l == null then {} else xl.l.keys) 
                                    + {xl.k} + (if xl.r == null then {} else xl.r.keys));
        Br' := xl.Set_repr(Br', (if xl.l == null then {} else xl.l.repr) 
                                    + {xl} + (if xl.r == null then {} else xl.r.repr));
        Br' := xl.Set_black(Br', true);
        Br' := xl.Set_black_height(Br', xl.black_height + 1);

        Br' := AssertLCAndRemove(Br', p);
        Br' := AssertLCAndRemove(Br', xl);
        Br' := AssertLCAndRemove(Br', oldr);
        
        ret := xl;
    } else {
        var xlr := xl.r;
        var xll := xl.l;

        if xlr != null {
            IfNotBr_ThenLC(Br', xlr);
        }
        if xll != null {
            IfNotBr_ThenLC(Br', xll);
        }

        if xll != null && !xll.black {
            fixed := true;
            Br' := x.Set_l(Br', xlr);
            if xlr != null {
                Br' := xlr.Set_p(Br', x);
            }
            Br' := xl.Set_r(Br', x);
            Br' := x.Set_p(Br', xl);
            Br' := xl.Set_p(Br', null);

            var oldxblack := x.black;
            
            if xll != null && !xll.black {
                Br' := xll.Set_black_height(Br', xll.black_height + 1);
            }
            Br' := xll.Set_black(Br', true);

            Br' := x.Set_min(Br', if x.l == null then x.k else x.l.min);
            Br' := x.Set_max(Br', if x.r == null then x.k else x.r.max);
            Br' := x.Set_keys(Br', (if x.l == null then {} else x.l.keys) 
                                        + {x.k} + (if x.r == null then {} else x.r.keys));
            Br' := x.Set_repr(Br', (if x.l == null then {} else x.l.repr) 
                                        + {x} + (if x.r == null then {} else x.r.repr));
            Br' := x.Set_black(Br', true);
            ghost var bh := MaxNat(GetBlackHeight(x.l), GetBlackHeight(x.r));
            Br' := x.Set_black_height(Br', bh + 1);

            Br' := xl.Set_min(Br', if xl.l == null then xl.k else xl.l.min);
            Br' := xl.Set_max(Br', if xl.r == null then xl.k else xl.r.max);
            Br' := xl.Set_keys(Br', (if xl.l == null then {} else xl.l.keys) 
                                        + {xl.k} + (if xl.r == null then {} else xl.r.keys));
            Br' := xl.Set_repr(Br', (if xl.l == null then {} else xl.l.repr) 
                                        + {xl} + (if xl.r == null then {} else xl.r.repr));
            Br' := xl.Set_black(Br', oldxblack);
            bh := MaxNat(GetBlackHeight(xl.l), GetBlackHeight(xl.r));
            if xl.black {
                Br' := xl.Set_black_height(Br', bh + 1);
            } else {
                Br' := xl.Set_black_height(Br', bh);
            }

            Br' := AssertLCAndRemove(Br', xlr);
            Br' := AssertLCAndRemove(Br', xll);
            Br' := AssertLCAndRemove(Br', x);
            Br' := AssertLCAndRemove(Br', xl);

            ret := xl;
        } else if xlr == null || xlr.black {
            fixed := !x.black;
            if xl.black {
                Br' := xl.Set_black_height(Br', xl.black_height - 1);
            }
            Br' := xl.Set_black(Br', false);
            Br' := x.Set_black(Br', true);
            var bh := MaxNat(GetBlackHeight(x.l), GetBlackHeight(x.r));
            Br' := x.Set_black_height(Br', bh + 1);
            Br' := x.Set_p(Br', null);

            Br' := AssertLCAndRemove(Br', xl);
            Br' := AssertLCAndRemove(Br', x);

            ret := x;
        } else {
            fixed := true;
            var xlrr := xlr.r;
            var xlrl := xlr.l;

            if xlrr != null {
                IfNotBr_ThenLC(Br', xlrr);
            }
            if xlrl != null {
                IfNotBr_ThenLC(Br', xlrl);
            }

            Br' := xl.Set_r(Br', xlrl);
            if xlrl != null {
                Br' := xlrl.Set_p(Br', xl);
            }
            Br' := xlr.Set_l(Br', xl);
            Br' := xl.Set_p(Br', xlr);
            Br' := xlr.Set_r(Br', x);
            Br' := x.Set_p(Br', xlr);
            Br' := x.Set_l(Br', xlrr);
            if xlrr != null {
                Br' := xlrr.Set_p(Br', x);
            }
            Br' := xlr.Set_p(Br', null);

            var oldxblack := x.black;

            Br' := x.Set_min(Br', if x.l == null then x.k else x.l.min);
            Br' := x.Set_max(Br', if x.r == null then x.k else x.r.max);
            Br' := x.Set_keys(Br', (if x.l == null then {} else x.l.keys) 
                                        + {x.k} + (if x.r == null then {} else x.r.keys));
            Br' := x.Set_repr(Br', (if x.l == null then {} else x.l.repr) 
                                        + {x} + (if x.r == null then {} else x.r.repr));
            Br' := x.Set_black(Br', true);
            ghost var bh := MaxNat(GetBlackHeight(x.l), GetBlackHeight(x.r));
            Br' := x.Set_black_height(Br', bh + 1);

            Br' := xl.Set_min(Br', if xl.l == null then xl.k else xl.l.min);
            Br' := xl.Set_max(Br', if xl.r == null then xl.k else xl.r.max);
            Br' := xl.Set_keys(Br', (if xl.l == null then {} else xl.l.keys) 
                                        + {xl.k} + (if xl.r == null then {} else xl.r.keys));
            Br' := xl.Set_repr(Br', (if xl.l == null then {} else xl.l.repr) 
                                        + {xl} + (if xl.r == null then {} else xl.r.repr));

            Br' := xlr.Set_min(Br', if xlr.l == null then xlr.k else xlr.l.min);
            Br' := xlr.Set_max(Br', if xlr.r == null then xlr.k else xlr.r.max);
            Br' := xlr.Set_keys(Br', (if xlr.l == null then {} else xlr.l.keys) 
                                        + {xlr.k} + (if xlr.r == null then {} else xlr.r.keys));
            Br' := xlr.Set_repr(Br', (if xlr.l == null then {} else xlr.l.repr) 
                                        + {xlr} + (if xlr.r == null then {} else xlr.r.repr));
            Br' := xlr.Set_black(Br', oldxblack);
            bh := MaxNat(GetBlackHeight(xlr.l), GetBlackHeight(xlr.r));
            if xlr.black {
                Br' := xlr.Set_black_height(Br', bh + 1);
            } else {
                Br' := xlr.Set_black_height(Br', bh);
            }

            Br' := AssertLCAndRemove(Br', xlrr);
            Br' := AssertLCAndRemove(Br', xlrl);
            Br' := AssertLCAndRemove(Br', x);
            Br' := AssertLCAndRemove(Br', xl);
            Br' := AssertLCAndRemove(Br', xlr);

            ret := xlr;
        }
    }
}

