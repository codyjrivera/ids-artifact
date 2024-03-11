// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions"
// by Anonymous Authors.
// 
// Artifact by Anonymous Author, 2023-2024. 
//
// Verification of AVL Tree Insert.

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
 * AVL insertion.
 */
method AVLInsert(ghost Br: set<AVLNode>, x: AVLNode?, k: int) 
    returns (ghost Br': set<AVLNode>, ret: AVLNode)
    requires Br == {}
    requires x != null ==> x.LC()
    requires x != null ==> k !in x.keys
    modifies if x == null then {} else x.repr
    decreases if x == null then {} else x.repr
    ensures ret.LC()
    ensures ret.p == null
    ensures x != null && x != ret ==> x.p != old(x.p)
    ensures (x == null ==>
                ret.keys == {k}
                && ret.min == k == ret.max
                && ret.height == 1
                && fresh(ret.repr)
                && Br' == {})
    ensures (x != null ==>
                ret.keys == old(x.keys) + {k}
                && (ret.min == old(x.min) || ret.min == k)
                && (ret.max == old(x.max) || ret.max == k)
                && (ret.height == old(x.height) || ret.height == old(x.height) + 1)
                && fresh(ret.repr - old(x.repr))
                && (old(x.p) == null ==> Br' == {})
                && (old(x.p) != null ==> Br' == {old(x.p)}))
{
    Br' := Br;
    if (x == null) {
        var leaf;
        Br', leaf := AVLNode.Create(Br', k);
        Br' := leaf.Set_min(Br', k);
        Br' := leaf.Set_max(Br', k);
        Br' := leaf.Set_keys(Br', {leaf.k});
        Br' := leaf.Set_repr(Br', {leaf});
        Br' := leaf.Set_height(Br', 1);
        Br' := AssertLCAndRemove(Br', leaf);
        ret := leaf;
    } else if (k < x.k) {
        if (x.l != null) {
            IfNotBr_ThenLC(Br', x.l);
        }
        if (x.r != null) {
            IfNotBr_ThenLC(Br', x.r);
        }
        var tmp;
        Br', tmp := AVLInsert(Br', x.l, k);
        if (x.l != null) {
            IfNotBr_ThenLC(Br', x.l);
        }
        if (x.r != null) {
            IfNotBr_ThenLC(Br', x.r);
        }

        ghost var oldl := x.l;
        Br' := x.Set_l(Br', tmp);
        Br' := tmp.Set_p(Br', x);

        Br' := x.Set_min(Br', if x.l == null then x.k else x.l.min);
        Br' := x.Set_max(Br', if x.r == null then x.k else x.r.max);
        Br' := x.Set_keys(Br', x.l.keys + {x.k} + (if x.r == null then {} else x.r.keys));
        Br' := x.Set_repr(Br', x.l.repr + {x} + (if x.r == null then {} else x.r.repr));
        Br' := x.Set_height(Br', MaxNat(GetHeight(x.l), GetHeight(x.r)) + 1);
        Br' := x.Set_p(Br', null);

        Br' := AssertLCAndRemove(Br', tmp);
        Br' := AssertLCAndRemove(Br', oldl);

        Br', ret := AVLBalance(Br', x);
    } else {
        if (x.l != null) {
            IfNotBr_ThenLC(Br', x.l);
        }
        if (x.r != null) {
            IfNotBr_ThenLC(Br', x.r);
        }
        var tmp;
        Br', tmp := AVLInsert(Br', x.r, k);
        if (x.l != null) {
            IfNotBr_ThenLC(Br', x.l);
        }
        if (x.r != null) {
            IfNotBr_ThenLC(Br', x.r);
        }

        ghost var oldr := x.r;
        Br' := x.Set_r(Br', tmp);
        Br' := tmp.Set_p(Br', x);

        Br' := x.Set_min(Br', if x.l == null then x.k else x.l.min);
        Br' := x.Set_max(Br', if x.r == null then x.k else x.r.max);
        Br' := x.Set_keys(Br', (if x.l == null then {} else x.l.keys) + {x.k} + x.r.keys);
        Br' := x.Set_repr(Br', (if x.l == null then {} else x.l.repr) + {x} + x.r.repr);
        Br' := x.Set_height(Br', MaxNat(GetHeight(x.l), GetHeight(x.r)) + 1);
        Br' := x.Set_p(Br', null);

        Br' := AssertLCAndRemove(Br', tmp);
        Br' := AssertLCAndRemove(Br', oldr);

        Br', ret := AVLBalance(Br', x);
    }
}
