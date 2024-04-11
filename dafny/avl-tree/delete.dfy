// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions"
// by Adithya Murali, Cody Rivera, and P. Madhusudan.
// 
// Artifact by Cody Rivera, 2023-2024. 
//
// Verification of AVL Tree Delete.

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

function MaxNat(x: nat, y: nat): nat {
    if x > y then x else y
}

method {:extern} AVLFindMin(ghost Br: set<AVLNode>, x: AVLNode)
    returns (ghost Br': set<AVLNode>, ret: int)
    requires Br !! x.repr
    requires x.LC()
    ensures ret in x.keys
    ensures ret == x.min
    ensures Br' == Br

method {:extern} AVLBalance(ghost Br: set<AVLNode>, x: AVLNode)
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

/**
 * AVL deletion.
 */
method AVLDelete(ghost Br: set<AVLNode>, x: AVLNode, k: int)
    returns (ghost Br': set<AVLNode>, ret: AVLNode?, del: AVLNode?)
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
                && del != null)
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
                        && (ret.height == old(x.height) || ret.height == old(x.height) - 1))
                && (del == null ==> 
                        ret.p == old(x.p)
                        && ret.keys == old(x.keys)
                        && ret.min == old(x.min)
                        && ret.max == old(x.max)
                        && ret.repr == old(x.repr)
                        && ret.height == old(x.height)))
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
            Br' := x.Set_height(Br', 1);

            Br' := AssertLCAndRemove(Br', x);
            Br' := AssertLCAndRemove(Br', xr);

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
            Br' := x.Set_height(Br', 1);

            Br' := AssertLCAndRemove(Br', x);
            Br' := AssertLCAndRemove(Br', xl);

            ret := xl; del := x;
        } else {
            var min;
            Br', min := AVLFindMin(Br', xr);

            var n, minnode;
            Br', n, minnode := AVLDelete(Br', xr, min);

            IfNotBr_ThenLC(Br', xr);

            if minnode == null {
                IfNotBr_ThenLC(Br', x);
                ret := x;
                del := null;
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
            Br' := x.Set_height(Br', MaxNat(GetHeight(x.l), GetHeight(x.r)) + 1);

            Br' := AssertLCAndRemove(Br', n);

            Br', ret := AVLBalance(Br', x);
            del := minnode;
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
            return;
        }

        var n, delnode;
        Br', n, delnode := AVLDelete(Br', x.l, k);

        if x.l != null {
            IfNotBr_ThenLC(Br', x.l);
        }

        if delnode == null {
            IfNotBr_ThenLC(Br', x);
            ret := x;
            del := null;
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
        Br' := x.Set_height(Br', MaxNat(GetHeight(x.l), GetHeight(x.r)) + 1);

        Br' := AssertLCAndRemove(Br', n);
        
        Br', ret := AVLBalance(Br', x);
        del := delnode;
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
            return;
        }

        var n, delnode;
        Br', n, delnode := AVLDelete(Br', x.r, k);

        if x.r != null {
            IfNotBr_ThenLC(Br', x.r);
        }

        if delnode == null {
            IfNotBr_ThenLC(Br', x);
            ret := x;
            del := null;
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
        Br' := x.Set_height(Br', MaxNat(GetHeight(x.l), GetHeight(x.r)) + 1);

        Br' := AssertLCAndRemove(Br', n);
                
        Br', ret := AVLBalance(Br', x);
        del := delnode;
    }
}