// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions"
// by Anonymous Authors.
// 
// Artifact by Anonymous Author, 2023-2024. 
//
// Verification of RBT Left Fixup.

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
 * RBT left fixup.
 */
method RBTDeleteLeftFixup(ghost Br: set<RBTNode>, x: RBTNode)
    returns (ghost Br': set<RBTNode>, ret: RBTNode, fixed: bool)
    requires Br !! (x.repr - {x})
    requires x.LC_Trans_DoubleBlack()
    requires (x.l == null && x.r != null && x.r.black_height == 1)
            || (x.l != null && x.r != null && x.l.black_height + 1 == x.r.black_height)
    requires (x.l == null || x.l.black)
    requires (x.black || (x.r == null || x.r.black))
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

    if xr != null && !xr.black {
        var xrl := xr.l;
        if xrl != null {
            IfNotBr_ThenLC(Br', xrl);
        }
        if xr.r != null {
            IfNotBr_ThenLC(Br', xr.r);
        }
        Br' := x.Set_r(Br', xrl);
        if xrl != null {
            Br' := xrl.Set_p(Br', x);
        }
        Br' := xr.Set_l(Br', x);
        Br' := x.Set_p(Br', xr);

        Br' := AssertLCAndRemove(Br', xrl);
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
        Br', p, fixed := RBTDeleteLeftFixup(Br', x);

        IfNotBr_ThenLC(Br', x);

        ghost var oldl := xr.l;
        Br' := xr.Set_l(Br', p);
        Br' := p.Set_p(Br', xr);
        Br' := xr.Set_p(Br', null);

        Br' := xr.Set_min(Br', if xr.l == null then xr.k else xr.l.min);
        Br' := xr.Set_max(Br', if xr.r == null then xr.k else xr.r.max);
        Br' := xr.Set_keys(Br', (if xr.l == null then {} else xr.l.keys) 
                                    + {xr.k} + (if xr.r == null then {} else xr.r.keys));
        Br' := xr.Set_repr(Br', (if xr.l == null then {} else xr.l.repr) 
                                    + {xr} + (if xr.r == null then {} else xr.r.repr));
        Br' := xr.Set_black(Br', true);
        Br' := xr.Set_black_height(Br', xr.black_height + 1);

        Br' := AssertLCAndRemove(Br', p);
        Br' := AssertLCAndRemove(Br', xr);
        Br' := AssertLCAndRemove(Br', oldl);
        
        ret := xr;
    } else {
        var xrl := xr.l;
        var xrr := xr.r;

        if xrl != null {
            IfNotBr_ThenLC(Br', xrl);
        }
        if xrr != null {
            IfNotBr_ThenLC(Br', xrr);
        }

        if xrr != null && !xrr.black {
            fixed := true;
            Br' := x.Set_r(Br', xrl);
            if xrl != null {
                Br' := xrl.Set_p(Br', x);
            }
            Br' := xr.Set_l(Br', x);
            Br' := x.Set_p(Br', xr);
            Br' := xr.Set_p(Br', null);

            var oldxblack := x.black;
            
            if xrr != null && !xrr.black {
                Br' := xrr.Set_black_height(Br', xrr.black_height + 1);
            }
            Br' := xrr.Set_black(Br', true);

            Br' := x.Set_min(Br', if x.l == null then x.k else x.l.min);
            Br' := x.Set_max(Br', if x.r == null then x.k else x.r.max);
            Br' := x.Set_keys(Br', (if x.l == null then {} else x.l.keys) 
                                        + {x.k} + (if x.r == null then {} else x.r.keys));
            Br' := x.Set_repr(Br', (if x.l == null then {} else x.l.repr) 
                                        + {x} + (if x.r == null then {} else x.r.repr));
            Br' := x.Set_black(Br', true);
            ghost var bh := MaxNat(GetBlackHeight(x.l), GetBlackHeight(x.r));
            Br' := x.Set_black_height(Br', bh + 1);

            Br' := xr.Set_min(Br', if xr.l == null then xr.k else xr.l.min);
            Br' := xr.Set_max(Br', if xr.r == null then xr.k else xr.r.max);
            Br' := xr.Set_keys(Br', (if xr.l == null then {} else xr.l.keys) 
                                        + {xr.k} + (if xr.r == null then {} else xr.r.keys));
            Br' := xr.Set_repr(Br', (if xr.l == null then {} else xr.l.repr) 
                                        + {xr} + (if xr.r == null then {} else xr.r.repr));
            Br' := xr.Set_black(Br', oldxblack);
            bh := MaxNat(GetBlackHeight(xr.l), GetBlackHeight(xr.r));
            if xr.black {
                Br' := xr.Set_black_height(Br', bh + 1);
            } else {
                Br' := xr.Set_black_height(Br', bh);
            }

            Br' := AssertLCAndRemove(Br', xrl);
            Br' := AssertLCAndRemove(Br', xrr);
            Br' := AssertLCAndRemove(Br', x);
            Br' := AssertLCAndRemove(Br', xr);

            ret := xr;
        } else if xrl == null || xrl.black {
            fixed := !x.black;
            if xr.black {
                Br' := xr.Set_black_height(Br', xr.black_height - 1);
            }
            Br' := xr.Set_black(Br', false);
            Br' := x.Set_black(Br', true);
            var bh := MaxNat(GetBlackHeight(x.l), GetBlackHeight(x.r));
            Br' := x.Set_black_height(Br', bh + 1);
            Br' := x.Set_p(Br', null);

            Br' := AssertLCAndRemove(Br', xr);
            Br' := AssertLCAndRemove(Br', x);

            ret := x;
        } else {
            fixed := true;
            var xrll := xrl.l;
            var xrlr := xrl.r;

            if xrll != null {
                IfNotBr_ThenLC(Br', xrll);
            }
            if xrlr != null {
                IfNotBr_ThenLC(Br', xrlr);
            }

            Br' := xr.Set_l(Br', xrlr);
            if xrlr != null {
                Br' := xrlr.Set_p(Br', xr);
            }
            Br' := xrl.Set_r(Br', xr);
            Br' := xr.Set_p(Br', xrl);
            Br' := xrl.Set_l(Br', x);
            Br' := x.Set_p(Br', xrl);
            Br' := x.Set_r(Br', xrll);
            if xrll != null {
                Br' := xrll.Set_p(Br', x);
            }
            Br' := xrl.Set_p(Br', null);

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

            Br' := xr.Set_min(Br', if xr.l == null then xr.k else xr.l.min);
            Br' := xr.Set_max(Br', if xr.r == null then xr.k else xr.r.max);
            Br' := xr.Set_keys(Br', (if xr.l == null then {} else xr.l.keys) 
                                        + {xr.k} + (if xr.r == null then {} else xr.r.keys));
            Br' := xr.Set_repr(Br', (if xr.l == null then {} else xr.l.repr) 
                                        + {xr} + (if xr.r == null then {} else xr.r.repr));

            Br' := xrl.Set_min(Br', if xrl.l == null then xrl.k else xrl.l.min);
            Br' := xrl.Set_max(Br', if xrl.r == null then xrl.k else xrl.r.max);
            Br' := xrl.Set_keys(Br', (if xrl.l == null then {} else xrl.l.keys) 
                                        + {xrl.k} + (if xrl.r == null then {} else xrl.r.keys));
            Br' := xrl.Set_repr(Br', (if xrl.l == null then {} else xrl.l.repr) 
                                        + {xrl} + (if xrl.r == null then {} else xrl.r.repr));
            Br' := xrl.Set_black(Br', oldxblack);
            bh := MaxNat(GetBlackHeight(xrl.l), GetBlackHeight(xrl.r));
            if xrl.black {
                Br' := xrl.Set_black_height(Br', bh + 1);
            } else {
                Br' := xrl.Set_black_height(Br', bh);
            }

            Br' := AssertLCAndRemove(Br', xrll);
            Br' := AssertLCAndRemove(Br', xrlr);
            Br' := AssertLCAndRemove(Br', x);
            Br' := AssertLCAndRemove(Br', xr);
            Br' := AssertLCAndRemove(Br', xrl);

            ret := xrl;
        }
    }
}

