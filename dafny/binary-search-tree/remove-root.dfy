// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions"
// by Adithya Murali, Cody Rivera, and P. Madhusudan.
// 
// Artifact by Cody Rivera, 2023-2024. 
//
// Verification of BST Remove Root.

include "binary-search-tree.dfy"

method BSTRemoveRoot(ghost Br: set<BSTNode>, x: BSTNode)
    returns (ghost Br': set<BSTNode>, ret: BSTNode?, root: BSTNode)
    requires x.repr !! Br
    requires x.LC()
    modifies x.repr
    decreases x.repr
    ensures ret == null || ret == old(x.l) || ret == old(x.r)
    ensures (old(x.keys) == {x.k} ==> ret == null)
    ensures (old(x.keys) > {x.k} ==> ret != null)
    ensures (ret != null ==> 
                ret.LC()
                && ret.p == null
                && ret.keys == old(x.keys) - {x.k}
                && ret.min >= old(x.min)
                && ret.max <= old(x.max)
                && ret.repr <= old(x.repr))
    ensures root == x && root.k == old(x.k)
    ensures root.LC() && root.Isolated()
    ensures old(x.p) == null ==> Br' == Br 
    ensures old(x.p) != null ==> Br' == Br + {old(x.p)}
{
    Br' := Br;
    if (x.l == null && x.r == null) {
        Br' := x.Set_p(Br', null);
        Br' := AssertLCAndRemove(Br', x);
        ret := null; root := x;
    } else if (x.l == null) {
        IfNotBr_ThenLC(Br', x.r);
        var r := x.r;
        Br' := r.Set_p(Br', null);

        Br' := x.Set_r(Br', null);
        Br' := x.Set_max(Br', x.k);
        Br' := x.Set_keys(Br', {x.k});
        Br' := x.Set_repr(Br', {x});
        Br' := x.Set_p(Br', null);

        Br' := AssertLCAndRemove(Br', r);
        Br' := AssertLCAndRemove(Br', x);
        //BSTNotIn_Keyset(Br, r, x.k);

        ret := r; root := x;
    } else if (x.r == null) {
        IfNotBr_ThenLC(Br', x.l);
        var l := x.l;
        Br' := l.Set_p(Br', null);

        Br' := x.Set_l(Br', null);
        Br' := x.Set_min(Br', x.k);
        Br' := x.Set_keys(Br', {x.k});
        Br' := x.Set_repr(Br', {x});
        Br' := x.Set_p(Br', null);

        Br' := AssertLCAndRemove(Br', l);
        Br' := AssertLCAndRemove(Br', x);
        //BSTNotIn_Keyset(Br, l, x.k);

        ret := l; root := x;
    } else {
        IfNotBr_ThenLC(Br', x.l);
        IfNotBr_ThenLC(Br', x.r);
        if (x.r.l != null) {
            IfNotBr_ThenLC(Br', x.r.l);
        }
        if (x.r.r != null) {
            IfNotBr_ThenLC(Br', x.r.r);
        }

        var r := x.r;
        var r_l := r.l;

        Br' := x.Set_r(Br', r_l);
        if (r_l != null) {
            Br' := r_l.Set_p(Br', x);
        }
        Br' := x.Set_max(Br', if x.r == null then x.k else x.r.max);
        Br' := x.Set_keys(Br', x.l.keys + {x.k} + (if x.r == null then {} else x.r.keys));
        Br' := x.Set_repr(Br', x.l.repr + {x} + (if x.r == null then {} else x.r.repr));

        Br' := r.Set_l(Br', null);
        Br' := r.Set_p(Br', null);
        Br' := r.Set_min(Br', r.k);
        Br' := r.Set_keys(Br', {r.k} + (if r.r == null then {} else r.r.keys));
        Br' := r.Set_repr(Br', {r} + (if r.r == null then {} else r.r.repr));

        Br' := AssertLCAndRemove(Br', x);
        Br' := AssertLCAndRemove(Br', r_l);
        Br' := AssertLCAndRemove(Br', r);
        //BSTNotIn_Keyset(Br, r, x.k);

        var tmp;
        Br', tmp, root := BSTRemoveRoot(Br', x);

        Br' := r.Set_l(Br', tmp);
        if (tmp != null) {
            Br' := tmp.Set_p(Br', r);
        }
        Br' := r.Set_p(Br', null);
        Br' := r.Set_min(Br', if r.l == null then r.k else r.l.min);
        Br' := r.Set_keys(
            Br', 
            (if r.l == null then {} else r.l.keys)
            + {r.k} + (if r.r == null then {} else r.r.keys)
        );
        Br' := r.Set_repr(
            Br', 
            (if r.l == null then {} else r.l.repr)
            + {r} + (if r.r == null then {} else r.r.repr)
        );
        Br' := AssertLCAndRemove(Br', r);
        Br' := AssertLCAndRemove(Br', r.l);

        ret := r;
    }
}
