// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions"
// by Anonymous Authors.
// 
// Artifact by Anonymous Author, 2023. 
//
// Verification of BST+Scaffolding Remove Root Inside.

include "bst-scaffolding.dfy"

ghost method BSTFixDepth(Br: set<BSTNode>, x: BSTNode)
    returns (Br': set<BSTNode>)
    requires (x.repr - {x}) !! Br
    requires x.LC_Trans_NoDepth() && x.p != null
    modifies x.repr * x.root.repr
    decreases x.repr
    ensures x.LC()
    ensures x.k == old(x.k)
    ensures x.l == old(x.l)
    ensures x.r == old(x.r)
    ensures x.p == old(x.p)
    ensures x.min == old(x.min)
    ensures x.max == old(x.max)
    ensures x.keys == old(x.keys)
    ensures x.repr == old(x.repr)
    ensures x.root == old(x.root)
    ensures Br' == Br - {x}

/**
 * BST remove root.
 */
method BSTRemoveRootInside(ghost Br: set<BSTNode>, x: BSTNode)
    returns (ghost Br': set<BSTNode>, ret: BSTNode?, root: BSTNode)
    requires x.repr !! Br
    requires x.LC() && x.p != null
    requires x.p.l == x || x.p.r == x
    requires !(x.p.l == x && x.p.r == x)
    modifies x.repr * x.root.repr, x.p
    decreases x.repr
    ensures ret == null || ret == old(x.l) || ret == old(x.r)
    ensures (old(x.repr) == {x} ==> ret == null)
    ensures (old(x.repr) > {x} ==> ret != null)
    ensures (ret != null ==> 
                ret.LC()
                && ret.keys == old(x.keys) - {x.k}
                && ret.min >= old(x.min)
                && ret.max <= old(x.max)
                && ret.repr == old(x.repr) - {x}
                && ret.root == old(x.root)
                && ret.p == old(x.p))
    ensures old(x.p.l) == x ==> old(x.p).l == ret
    ensures old(x.p.l) != x ==> old(x.p).l == old(x.p.l)
    ensures old(x.p.r) == x ==> old(x.p).r == ret
    ensures old(x.p.r) != x ==> old(x.p).r == old(x.p.r)
    ensures old(x.p.k) == old(x.p).k
    ensures old(x.p.p) == old(x.p).p
    ensures old(x.p.keys) == old(x.p).keys
    ensures old(x.p.repr) == old(x.p).repr
    ensures old(x.p.min) == old(x.p).min
    ensures old(x.p.max) == old(x.p).max
    ensures old(x.p.depth) == old(x.p).depth
    ensures old(x.p.root) == old(x.p).root
    ensures root == x && root.k == old(x.k)
    ensures root.LC() && root.Isolated()
    ensures old(x.p) == null ==> Br' == Br 
    ensures old(x.p) != null ==> Br' == Br + {old(x.p)}
{
    Br' := Br;
    var p := x.p;
    if (x.l == null && x.r == null) {
        Br' := x.Set_root(Br', x);
        Br' := x.Set_depth(Br', 0);
        Br' := x.Set_keys(Br', {});
        Br' := x.Set_p(Br', null);

        if p.l == x {
            Br' := p.Set_l(Br', null);
        } else {
            Br' := p.Set_r(Br', null);
        }
        Br' := AssertLCAndRemove(Br', x);

        Br' := AssertLCAndRemove(Br', x);
        ret := null; root := x;
    } else if (x.l == null) {
        IfNotBr_ThenLC(Br', x.r);
        var r := x.r;

        Br' := x.Set_r(Br', null);
        Br' := x.Set_max(Br', x.k);
        Br' := x.Set_keys(Br', {});
        Br' := x.Set_repr(Br', {x});
        Br' := x.Set_root(Br', x);
        Br' := x.Set_depth(Br', 0);
        Br' := x.Set_p(Br', null);
        Br' := AssertLCAndRemove(Br', x);

        Br' := r.Set_p(Br', p);
        if p != null {
            if p.l == x {
                Br' := p.Set_l(Br', r);
            } else {
                Br' := p.Set_r(Br', r);
            }
            Br' := AssertLCAndRemove(Br', x);
        }

        Br' := BSTFixDepth(Br', r);
        Br' := AssertLCAndRemove(Br', r);

        ret := r; root := x;
    } else if (x.r == null) {
        IfNotBr_ThenLC(Br', x.l);
        var l := x.l;

        Br' := x.Set_l(Br', null);
        Br' := x.Set_max(Br', x.k);
        Br' := x.Set_keys(Br', {});
        Br' := x.Set_repr(Br', {x});
        Br' := x.Set_root(Br', x);
        Br' := x.Set_depth(Br', 0);
        Br' := x.Set_p(Br', null);
        Br' := AssertLCAndRemove(Br', x);

        Br' := l.Set_p(Br', p);
        if p != null {
            if p.l == x {
                Br' := p.Set_l(Br', l);
            } else {
                Br' := p.Set_r(Br', l);
            }
            Br' := AssertLCAndRemove(Br', x);
        }

        Br' := BSTFixDepth(Br', l);
        Br' := AssertLCAndRemove(Br', l);

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
            Br' := BSTFixDepth(Br', r_l);
        }

        Br' := x.Set_max(Br', if x.r == null then x.k else x.r.max);
        Br' := x.Set_keys(Br', x.l.keys + {x.k} + (if x.r == null then {} else x.r.keys));
        Br' := x.Set_repr(Br', x.l.repr + {x} + (if x.r == null then {} else x.r.repr));

        Br' := r.Set_l(Br', null);
        Br' := r.Set_p(Br', x.p);
        Br' := r.Set_min(Br', r.k);
        Br' := r.Set_keys(Br', {r.k} + (if r.r == null then {} else r.r.keys));
        Br' := r.Set_repr(Br', {r} + (if r.r == null then {} else r.r.repr));

        Br' := AssertLCAndRemove(Br', x);
        Br' := AssertLCAndRemove(Br', r_l);

        // Awkward change to non-ghost code.
        var fix_p_l := p.l == x;
        var fix_p_r := p.r == x;

        var tmp;
        Br', tmp, root := BSTRemoveRootInside(Br', x);

        Br' := r.Set_l(Br', tmp);
        if (tmp != null) {
            Br' := tmp.Set_p(Br', r);
        }
        Br' := r.Set_p(Br', p);
        if fix_p_l {
            Br' := p.Set_l(Br', r);
        } 
        if fix_p_r {
            Br' := p.Set_r(Br', r);
        }
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
        Br' := r.Set_depth(Br', 1 + r.p.depth);
        
        Br' := BSTFixDepth(Br', r.l);
        if r.r != null {
            Br' := BSTFixDepth(Br', r.r);
        }
        Br' := AssertLCAndRemove(Br', r.l);
        Br' := AssertLCAndRemove(Br', r.r);
        Br' := AssertLCAndRemove(Br', r);
    
        ret := r;
    }
}
