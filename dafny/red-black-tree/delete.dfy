// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions"
// by Anonymous Authors.
// 
// Artifact by Anonymous Author, 2023-2024. 
//
// Verification of RBT Delete.

include "red-black-tree.dfy"

method {:extern} RBTFindMin(ghost Br: set<RBTNode>, x: RBTNode)
    returns (ghost Br': set<RBTNode>, ret: int)
    requires Br !! x.repr
    requires x.LC()
    ensures ret in x.keys
    ensures ret == x.min
    ensures Br' == Br

method {:extern} RBTDeleteLeftFixup(ghost Br: set<RBTNode>, x: RBTNode)
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

method {:extern} RBTDeleteRightFixup(ghost Br: set<RBTNode>, x: RBTNode)
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

/**
 * RBT deletion.
 */
method RBTDelete(ghost Br: set<RBTNode>, x: RBTNode, k: int)
    returns (ghost Br': set<RBTNode>, ret: RBTNode?, del: RBTNode?, fixed: bool)
    requires Br == {}
    requires x.LC() //&& k in x.keys
    modifies x.repr
    decreases x.repr
    ensures x != ret && x != del ==> x.p != old(x.p)
    ensures ret != del
    ensures x !in Br'
    //ensures (old(x.keys) == {k} ==> ret == null)
    //ensures (old(x.keys) > {k} ==> ret != null)
    ensures (ret == null ==> 
                old(x.keys) == {k}
                && old(x.repr) == {x}
                && del != null
                && ((fixed && !old(x.black)) || (!fixed && old(x.black))))
    ensures (ret != null ==> 
                ret.LC()
                && (del != null ==> 
                        ret.p == null
                        && ret.keys == old(x.keys) - {k}
                        && (k == old(x.min) ==> ret.min > old(x.min))
                        && (k != old(x.min) ==> ret.min == old(x.min))
                        && (k == old(x.max) ==> ret.max < old(x.max))
                        && (k != old(x.max) ==> ret.max == old(x.max))
                        && ret.repr == old(x.repr) - {del}
                        && (ret.black || (!ret.black && !old(x.black)))
                        && ((ret.black_height == old(x.black_height) && fixed)
                                || (ret.black_height == old(x.black_height) - 1 && !fixed && old(x.black))))
                && (del == null ==> 
                        ret.p == old(x.p)
                        && ret.keys == old(x.keys)
                        && ret.min == old(x.min)
                        && ret.max == old(x.max)
                        && ret.repr == old(x.repr)
                        && ret.black == old(x.black)
                        && ret.black_height == old(x.black_height)))
    //ensures del != null ==> del.k == k && k in old(x.keys)
    ensures del != null ==> del.LC() && del.Isolated() && k in old(x.keys) && del in old(x.repr)
    ensures del == null || old(x.p) == null ==> Br' == {}
    ensures del != null && old(x.p) != null ==> Br' == {old(x.p)}
{
    Br' := Br;
    if k == x.k {
        var xl := x.l;
        var xr := x.r;

        if xl != null {
            IfNotBr_ThenLC(Br', xl);
        }
        if xr != null {
            IfNotBr_ThenLC(Br', xr);
        }

        if xl == null && xr == null {
            Br' := x.Set_p(Br', null);
            Br' := AssertLCAndRemove(Br', x);
            fixed := !x.black;
            ret := null; del := x;
        } else if xl == null {
            Br' := x.Set_p(Br', null);
            Br' := x.Set_l(Br', null);
            Br' := x.Set_r(Br', null);
            Br' := xr.Set_p(Br', null);
            Br' := x.Set_min(Br', x.k);
            Br' := x.Set_max(Br', x.k);
            Br' := x.Set_repr(Br', {x});
            Br' := x.Set_keys(Br', {x.k});
            Br' := xr.Set_black(Br', true);
            Br' := xr.Set_black_height(Br', xr.black_height + 1);

            Br' := AssertLCAndRemove(Br', x);
            Br' := AssertLCAndRemove(Br', xr);

            fixed := true;
            ret := xr; del := x;
        } else if xr == null {
            Br' := x.Set_p(Br', null);
            Br' := x.Set_l(Br', null);
            Br' := x.Set_r(Br', null);
            Br' := xl.Set_p(Br', null);
            Br' := x.Set_min(Br', x.k);
            Br' := x.Set_max(Br', x.k);
            Br' := x.Set_repr(Br', {x});
            Br' := x.Set_keys(Br', {x.k});
            Br' := xl.Set_black(Br', true);
            Br' := xl.Set_black_height(Br', xl.black_height + 1);

            Br' := AssertLCAndRemove(Br', x);
            Br' := AssertLCAndRemove(Br', xl);

            fixed := true;
            ret := xl; del := x;
        } else {
            var min;
            Br', min := RBTFindMin(Br', xr);

            var n, minnode;
            Br', n, minnode, fixed := RBTDelete(Br', xr, min);

            IfNotBr_ThenLC(Br', xr);

            if minnode == null {
                IfNotBr_ThenLC(Br', x);
                ret := x;
                del := null;
                fixed := true;
                return;
            }

            Br' := x.Set_k(Br', min);
            Br' := x.Set_p(Br', null);
            Br' := x.Set_r(Br', n);
            if n != null {
                Br' := n.Set_p(Br', x);
            }
            Br' := AssertLCAndRemove(Br', xr);

            Br' := x.Set_min(Br', if x.l == null then x.k else x.l.min);
            Br' := x.Set_max(Br', if x.r == null then x.k else x.r.max);
            Br' := x.Set_keys(Br', (if x.l == null then {} else x.l.keys) 
                                        + {x.k} + (if x.r == null then {} else x.r.keys));
            Br' := x.Set_repr(Br', (if x.l == null then {} else x.l.repr) 
                                        + {x} + (if x.r == null then {} else x.r.repr));

            Br' := AssertLCAndRemove(Br', n);

            if fixed {
                Br' := AssertLCAndRemove(Br', x);

                ret := x; del := minnode;
                fixed := true;
            } else {
                Br', ret, fixed := RBTDeleteRightFixup(Br', x);
                del := minnode;
            }
        }
    } else if k < x.k {
        if x.l != null {
            IfNotBr_ThenLC(Br', x.l);
        }
        if x.r != null {
            IfNotBr_ThenLC(Br', x.r);
        }

        if x.l == null {
            ret := x;
            del := null;
            fixed := true;
            return;
        }

        var n, delnode;
        Br', n, delnode, fixed := RBTDelete(Br', x.l, k);

        if x.l != null {
            IfNotBr_ThenLC(Br', x.l);
        }

        if delnode == null {
            IfNotBr_ThenLC(Br', x);
            ret := x;
            del := null;
            fixed := true;
            return;
        }

        Br' := x.Set_p(Br', null);
        ghost var oldl := x.l;
        Br' := x.Set_l(Br', n);
        if n != null {
            Br' := n.Set_p(Br', x);
        }
        Br' := AssertLCAndRemove(Br', oldl);

        Br' := x.Set_min(Br', if x.l == null then x.k else x.l.min);
        Br' := x.Set_max(Br', if x.r == null then x.k else x.r.max);
        Br' := x.Set_keys(Br', (if x.l == null then {} else x.l.keys) 
                                    + {x.k} + (if x.r == null then {} else x.r.keys));
        Br' := x.Set_repr(Br', (if x.l == null then {} else x.l.repr) 
                                    + {x} + (if x.r == null then {} else x.r.repr));

        Br' := AssertLCAndRemove(Br', n);

        if fixed {
            Br' := AssertLCAndRemove(Br', x);

            ret := x; del := delnode;
            fixed := true;
        } else {
            Br', ret, fixed := RBTDeleteLeftFixup(Br', x);
            del := delnode;
        }
    } else {
        if x.l != null {
            IfNotBr_ThenLC(Br', x.l);
        }
        if x.r != null {
            IfNotBr_ThenLC(Br', x.r);
        }

        if x.r == null {
            ret := x;
            del := null;
            fixed := true;
            return;
        }

        var n, delnode;
        Br', n, delnode, fixed := RBTDelete(Br', x.r, k);

        if x.r != null {
            IfNotBr_ThenLC(Br', x.r);
        }

        if delnode == null {
            IfNotBr_ThenLC(Br', x);
            ret := x;
            del := null;
            fixed := true;
            return;
        }

        Br' := x.Set_p(Br', null);
        ghost var oldr := x.r;
        Br' := x.Set_r(Br', n);
        if n != null {
            Br' := n.Set_p(Br', x);
        }
        Br' := AssertLCAndRemove(Br', oldr);

        Br' := x.Set_min(Br', if x.l == null then x.k else x.l.min);
        Br' := x.Set_max(Br', if x.r == null then x.k else x.r.max);
        Br' := x.Set_keys(Br', (if x.l == null then {} else x.l.keys) 
                                    + {x.k} + (if x.r == null then {} else x.r.keys));
        Br' := x.Set_repr(Br', (if x.l == null then {} else x.l.repr) 
                                    + {x} + (if x.r == null then {} else x.r.repr));

        Br' := AssertLCAndRemove(Br', n);

        if fixed {
            Br' := AssertLCAndRemove(Br', x);

            ret := x; del := delnode;
            fixed := true;
        } else {
            Br', ret, fixed := RBTDeleteRightFixup(Br', x);
            del := delnode;
        }
    }
}