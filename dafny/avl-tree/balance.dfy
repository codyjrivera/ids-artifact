// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions"
// by Anonymous Authors.
// 
// Artifact by Anonymous Author, 2023-2024. 
//
// Verification of AVL Tree Balance.

include "avl-tree.dfy"

function GetHeight(x: AVLNode?): nat
    reads x
{
    if x == null then 0 else x.height
}

twostate function GetOldHeight(x: AVLNode?): nat
    reads x
{
    if x == null then 0 else old(x.height)
}

/**
 * AVL balance.
 */
 method AVLBalance(ghost Br: set<AVLNode>, x: AVLNode)
    returns (ghost Br': set<AVLNode>, ret: AVLNode)
    requires Br !! (x.repr - {x})
    requires x.LC_Trans_Unbalanced()
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
            && (ret.height == old(x.height) || ret.height == old(x.height) - 1)
            && (var diff := GetOldHeight(old(x.r)) - GetOldHeight(old(x.l));
                    -1 <= diff <= 1 ==> ret.height == old(x.height))
    ensures old(x.p) == null ==> Br' == Br - {x} 
    ensures old(x.p) != null ==> Br' == (Br - {x}) + {old(x.p)}
{
    Br' := Br;
    var xl := x.l;
    var xr := x.r;

    if xl != null {
        IfNotBr_ThenLC(Br', xl);
    }
    if xr != null {
        IfNotBr_ThenLC(Br', xr);
    }

    var diff := GetHeight(xr) - GetHeight(xl);

    // Already okay
    if -1 <= diff <= 1 {
        Br' := x.Set_p(Br', null);
        Br' := AssertLCAndRemove(Br', x);
        ret := x;
        return;
    }

    if diff == 2 {
        var rl := xr.l;
        var rr := xr.r;

        if rl != null {
            IfNotBr_ThenLC(Br', rl);
        }
        if rr != null {
            IfNotBr_ThenLC(Br', rr);
        }

        var rlht := GetHeight(rl);
        var rrht := GetHeight(rr);

        if rlht <= rrht {
            Br' := x.Set_r(Br', rl);
            if rl != null {
                Br' := rl.Set_p(Br', x);
            }
            Br' := x.Set_height(Br', rlht + 1);

            Br' := xr.Set_l(Br', x);
            Br' := x.Set_p(Br', xr);
            Br' := xr.Set_height(Br', rlht + 2);
            Br' := xr.Set_p(Br', null);

            Br' := x.Set_min(Br', if x.l == null then x.k else x.l.min);
            Br' := x.Set_max(Br', if x.r == null then x.k else x.r.max);
            Br' := x.Set_keys(Br', (if x.l == null then {} else x.l.keys) 
                                        + {x.k} + (if x.r == null then {} else x.r.keys));
            Br' := x.Set_repr(Br', (if x.l == null then {} else x.l.repr) 
                                        + {x} + (if x.r == null then {} else x.r.repr));

            Br' := xr.Set_min(Br', if xr.l == null then xr.k else xr.l.min);
            Br' := xr.Set_max(Br', if xr.r == null then xr.k else xr.r.max);
            Br' := xr.Set_keys(Br', (if xr.l == null then {} else xr.l.keys) 
                                        + {xr.k} + (if xr.r == null then {} else xr.r.keys));
            Br' := xr.Set_repr(Br', (if xr.l == null then {} else xr.l.repr) 
                                        + {xr} + (if xr.r == null then {} else xr.r.repr));

            Br' := AssertLCAndRemove(Br', rl);
            Br' := AssertLCAndRemove(Br', x);
            Br' := AssertLCAndRemove(Br', xr);

            ret := xr;
        } else {
            var rll := rl.l;
            var rlr := rl.r;

            if rll != null {
                IfNotBr_ThenLC(Br', rll);
            }
            if rlr != null {
                IfNotBr_ThenLC(Br', rlr);
            }

            var lht := GetHeight(xl);

            Br' := x.Set_r(Br', rll);
            if rll != null {
                Br' := rll.Set_p(Br', x);
            }
            Br' := x.Set_height(Br', lht + 1);

            Br' := xr.Set_l(Br', rlr);
            if rlr != null {
                Br' := rlr.Set_p(Br', xr);
            }
            Br' := xr.Set_height(Br', rrht + 1);

            Br' := rl.Set_l(Br', x);
            Br' := x.Set_p(Br', rl);
            Br' := rl.Set_r(Br', xr);
            Br' := xr.Set_p(Br', rl);
            Br' := rl.Set_height(Br', lht + 2);
            Br' := rl.Set_p(Br', null);

            Br' := x.Set_min(Br', if x.l == null then x.k else x.l.min);
            Br' := x.Set_max(Br', if x.r == null then x.k else x.r.max);
            Br' := x.Set_keys(Br', (if x.l == null then {} else x.l.keys) 
                                        + {x.k} + (if x.r == null then {} else x.r.keys));
            Br' := x.Set_repr(Br', (if x.l == null then {} else x.l.repr) 
                                        + {x} + (if x.r == null then {} else x.r.repr));

            Br' := xr.Set_min(Br', if xr.l == null then xr.k else xr.l.min);
            Br' := xr.Set_max(Br', if xr.r == null then xr.k else xr.r.max);
            Br' := xr.Set_keys(Br', (if xr.l == null then {} else xr.l.keys) 
                                        + {xr.k} + (if xr.r == null then {} else xr.r.keys));
            Br' := xr.Set_repr(Br', (if xr.l == null then {} else xr.l.repr) 
                                        + {xr} + (if xr.r == null then {} else xr.r.repr));

            Br' := rl.Set_min(Br', if rl.l == null then rl.k else rl.l.min);
            Br' := rl.Set_max(Br', if rl.r == null then rl.k else rl.r.max);
            Br' := rl.Set_keys(Br', (if rl.l == null then {} else rl.l.keys) 
                                        + {rl.k} + (if rl.r == null then {} else rl.r.keys));
            Br' := rl.Set_repr(Br', (if rl.l == null then {} else rl.l.repr) 
                                        + {rl} + (if rl.r == null then {} else rl.r.repr));

            Br' := AssertLCAndRemove(Br', rll);
            Br' := AssertLCAndRemove(Br', rlr);
            Br' := AssertLCAndRemove(Br', x);
            Br' := AssertLCAndRemove(Br', xr);
            Br' := AssertLCAndRemove(Br', rl);

            ret := rl;
        }
    } else { // diff == -2
        var lr := xl.r;
        var ll := xl.l;

        if lr != null {
            IfNotBr_ThenLC(Br', lr);
        }
        if ll != null {
            IfNotBr_ThenLC(Br', ll);
        }

        var lrht := GetHeight(lr);
        var llht := GetHeight(ll);

        if lrht <= llht {
            Br' := x.Set_l(Br', lr);
            if lr != null {
                Br' := lr.Set_p(Br', x);
            }
            Br' := x.Set_height(Br', lrht + 1);

            Br' := xl.Set_r(Br', x);
            Br' := x.Set_p(Br', xl);
            Br' := xl.Set_height(Br', lrht + 2);
            Br' := xl.Set_p(Br', null);

            Br' := x.Set_max(Br', if x.r == null then x.k else x.r.max);
            Br' := x.Set_min(Br', if x.l == null then x.k else x.l.min);
            Br' := x.Set_keys(Br', (if x.r == null then {} else x.r.keys) 
                                        + {x.k} + (if x.l == null then {} else x.l.keys));
            Br' := x.Set_repr(Br', (if x.r == null then {} else x.r.repr) 
                                        + {x} + (if x.l == null then {} else x.l.repr));

            Br' := xl.Set_max(Br', if xl.r == null then xl.k else xl.r.max);
            Br' := xl.Set_min(Br', if xl.l == null then xl.k else xl.l.min);
            Br' := xl.Set_keys(Br', (if xl.r == null then {} else xl.r.keys) 
                                        + {xl.k} + (if xl.l == null then {} else xl.l.keys));
            Br' := xl.Set_repr(Br', (if xl.r == null then {} else xl.r.repr) 
                                        + {xl} + (if xl.l == null then {} else xl.l.repr));

            Br' := AssertLCAndRemove(Br', lr);
            Br' := AssertLCAndRemove(Br', x);
            Br' := AssertLCAndRemove(Br', xl);

            ret := xl;
        } else {
            var lrr := lr.r;
            var lrl := lr.l;

            if lrr != null {
                IfNotBr_ThenLC(Br', lrr);
            }
            if lrl != null {
                IfNotBr_ThenLC(Br', lrl);
            }

            var rht := GetHeight(xr);

            Br' := x.Set_l(Br', lrr);
            if lrr != null {
                Br' := lrr.Set_p(Br', x);
            }
            Br' := x.Set_height(Br', rht + 1);

            Br' := xl.Set_r(Br', lrl);
            if lrl != null {
                Br' := lrl.Set_p(Br', xl);
            }
            Br' := xl.Set_height(Br', llht + 1);

            Br' := lr.Set_r(Br', x);
            Br' := x.Set_p(Br', lr);
            Br' := lr.Set_l(Br', xl);
            Br' := xl.Set_p(Br', lr);
            Br' := lr.Set_height(Br', rht + 2);
            Br' := lr.Set_p(Br', null);

            Br' := x.Set_max(Br', if x.r == null then x.k else x.r.max);
            Br' := x.Set_min(Br', if x.l == null then x.k else x.l.min);
            Br' := x.Set_keys(Br', (if x.r == null then {} else x.r.keys) 
                                        + {x.k} + (if x.l == null then {} else x.l.keys));
            Br' := x.Set_repr(Br', (if x.r == null then {} else x.r.repr) 
                                        + {x} + (if x.l == null then {} else x.l.repr));

            Br' := xl.Set_max(Br', if xl.r == null then xl.k else xl.r.max);
            Br' := xl.Set_min(Br', if xl.l == null then xl.k else xl.l.min);
            Br' := xl.Set_keys(Br', (if xl.r == null then {} else xl.r.keys) 
                                        + {xl.k} + (if xl.l == null then {} else xl.l.keys));
            Br' := xl.Set_repr(Br', (if xl.r == null then {} else xl.r.repr) 
                                        + {xl} + (if xl.l == null then {} else xl.l.repr));

            Br' := lr.Set_max(Br', if lr.r == null then lr.k else lr.r.max);
            Br' := lr.Set_min(Br', if lr.l == null then lr.k else lr.l.min);
            Br' := lr.Set_keys(Br', (if lr.r == null then {} else lr.r.keys) 
                                        + {lr.k} + (if lr.l == null then {} else lr.l.keys));
            Br' := lr.Set_repr(Br', (if lr.r == null then {} else lr.r.repr) 
                                        + {lr} + (if lr.l == null then {} else lr.l.repr));

            Br' := AssertLCAndRemove(Br', lrr);
            Br' := AssertLCAndRemove(Br', lrl);
            Br' := AssertLCAndRemove(Br', x);
            Br' := AssertLCAndRemove(Br', xl);
            Br' := AssertLCAndRemove(Br', lr);

            ret := lr;
        }
    }
}