// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions"
// by Anonymous Authors.
// 
// Artifact by Anonymous Author, 2023-2024. 
//
// Verification of BST Insert.

include "binary-search-tree.dfy"

method BSTInsert(ghost Br: set<BSTNode>, x: BSTNode?, k: int)
    returns (ghost Br': set<BSTNode>, ret: BSTNode)
    requires Br == {}
    requires x != null ==> x.LC()
    requires x != null ==> k !in x.keys
    modifies if x == null then {} else x.repr
    decreases if x == null then {} else x.repr
    ensures ret.LC()
    ensures ret.p == null
    ensures x != null ==> ret == x
    ensures (x == null ==>
                ret.keys == {k}
                && ret.min == k == ret.max
                && fresh(ret.repr)
                && Br' == {})
    ensures (x != null ==>
                ret.keys == old(x.keys) + {k}
                && (ret.min == old(x.min) || ret.min == k)
                && (ret.max == old(x.max) || ret.max == k)
                && fresh(ret.repr - old(x.repr))
                && (old(x.p) == null ==> Br' == {})
                && (old(x.p) != null ==> Br' == {old(x.p)}))
{
    Br' := Br;
    if (x == null) {
        var leaf;
        Br', leaf := BSTNode.Create(Br', k);
        Br' := leaf.Set_min(Br', k);
        Br' := leaf.Set_max(Br', k);
        Br' := leaf.Set_keys(Br', {leaf.k});
        Br' := leaf.Set_repr(Br', {leaf});
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
        Br', tmp := BSTInsert(Br', x.l, k);
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
        Br' := x.Set_p(Br', null);

        Br' := AssertLCAndRemove(Br', tmp);
        Br' := AssertLCAndRemove(Br', x);
        Br' := AssertLCAndRemove(Br', oldl);

        ret := x;
    } else {
        if (x.l != null) {
            IfNotBr_ThenLC(Br', x.l);
        }
        if (x.r != null) {
            IfNotBr_ThenLC(Br', x.r);
        }
        var tmp;
        Br', tmp := BSTInsert(Br', x.r, k);
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
        Br' := x.Set_p(Br', null);

        Br' := AssertLCAndRemove(Br', tmp);
        Br' := AssertLCAndRemove(Br', x);
        Br' := AssertLCAndRemove(Br', oldr);

        ret := x;
    }
}
