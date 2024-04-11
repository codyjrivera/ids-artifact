// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions"
// by Adithya Murali, Cody Rivera, and P. Madhusudan.
// 
// Artifact by Cody Rivera, 2023-2024. 
//
// Verification of Scheduler Queue Remove Root Inside.

include "scheduler-queue.dfy"

ghost method BSTFixDepth(Br: QueueBr, q: Queue, x: QueueNode)
    returns (Br': QueueBr)
    requires (x.bst_repr - {x}) !! Br.bst && Br.list == {}
    requires x.LC_Trans_NoDepth() && x.p != null
    modifies x.bst_repr * x.bst_root.bst_repr
    decreases x.bst_repr
    ensures x.LC()
    ensures x.k == old(x.k)
    ensures x.l == old(x.l)
    ensures x.r == old(x.r)
    ensures x.p == old(x.p)
    ensures x.min == old(x.min)
    ensures x.max == old(x.max)
    ensures x.bst_keys == old(x.bst_keys)
    ensures x.bst_repr == old(x.bst_repr)
    ensures x.bst_root == old(x.bst_root)
    ensures x.List_FieldsUnchanged()
    ensures q.q1s != null ==> q.q1s.List_FieldsUnchanged() && q.q1s.bst_root == old(q.q1s.bst_root)
    ensures Br'.bst == Br.bst - {x}
    ensures Br'.list == {}

method BSTRemoveRootInside(ghost Br: QueueBr, q: Queue, x: QueueNode)
    returns (ghost Br': QueueBr, ret: QueueNode?, root: QueueNode)
    requires x.bst_repr !! Br.bst && Br.list == {}
    requires x.LC() && x.p != null
    requires x.p.l == x || x.p.r == x
    requires !(x.p.l == x && x.p.r == x)
    requires x.next == null && x.prev == null
    requires q.q1s != null ==> x != q.q1s
    modifies x.bst_repr * x.bst_root.bst_repr, x.p
    decreases x.bst_repr
    ensures ret == null || ret == old(x.l) || ret == old(x.r)
    ensures (old(x.bst_repr) == {x} ==> ret == null)
    ensures (old(x.bst_repr) > {x} ==> ret != null)
    ensures (ret != null ==> 
                ret.LC()
                && ret.bst_keys == old(x.bst_keys) - {x.k}
                && ret.min >= old(x.min)
                && ret.max <= old(x.max)
                && ret.bst_repr == old(x.bst_repr) - {x}
                && ret.bst_root == old(x.bst_root)
                && ret.p == old(x.p)
                && ret.List_FieldsUnchanged())
    ensures old(x.p.l) == x ==> old(x.p).l == ret
    ensures old(x.p.l) != x ==> old(x.p).l == old(x.p.l)
    ensures old(x.p.r) == x ==> old(x.p).r == ret
    ensures old(x.p.r) != x ==> old(x.p).r == old(x.p.r)
    ensures old(x.p.k) == old(x.p).k
    ensures old(x.p.p) == old(x.p).p
    ensures old(x.p.bst_keys) == old(x.p).bst_keys
    ensures old(x.p.bst_repr) == old(x.p).bst_repr
    ensures old(x.p.min) == old(x.p).min
    ensures old(x.p.max) == old(x.p).max
    ensures old(x.p.bst_depth) == old(x.p).bst_depth
    ensures old(x.p.bst_root) == old(x.p).bst_root
    ensures old(x.p).List_FieldsUnchanged()
    ensures root == x && root.k == old(x.k)
    ensures root.LC() && root.BST_Isolated()
    ensures root.List_FieldsUnchanged()
    ensures q.q1s != null ==> q.q1s.List_FieldsUnchanged() && q.q1s.bst_root == old(q.q1s.bst_root)
    ensures old(x.p) == null ==> Br'.bst == Br.bst 
    ensures old(x.p) != null ==> Br'.bst == Br.bst + {old(x.p)}
    ensures Br'.list == {}
{
    Br' := Br;
    var p := x.p;
    if (x.l == null && x.r == null) {
        Br' := x.Set_bst_root(Br', x);
        Br' := x.Set_bst_depth(Br', 0);
        Br' := x.Set_bst_keys(Br', {});
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
        Br' := x.Set_bst_keys(Br', {});
        Br' := x.Set_bst_repr(Br', {x});
        Br' := x.Set_bst_root(Br', x);
        Br' := x.Set_bst_depth(Br', 0);
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

        Br' := BSTFixDepth(Br', q, r);
        Br' := AssertLCAndRemove(Br', r);

        ret := r; root := x;
    } else if (x.r == null) {
        IfNotBr_ThenLC(Br', x.l);
        var l := x.l;

        Br' := x.Set_l(Br', null);
        Br' := x.Set_max(Br', x.k);
        Br' := x.Set_bst_keys(Br', {});
        Br' := x.Set_bst_repr(Br', {x});
        Br' := x.Set_bst_root(Br', x);
        Br' := x.Set_bst_depth(Br', 0);
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

        Br' := BSTFixDepth(Br', q, l);
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
            Br' := BSTFixDepth(Br', q, r_l);
        }

        Br' := x.Set_max(Br', if x.r == null then x.k else x.r.max);
        Br' := x.Set_bst_keys(Br', x.l.bst_keys + {x.k} + (if x.r == null then {} else x.r.bst_keys));
        Br' := x.Set_bst_repr(Br', x.l.bst_repr + {x} + (if x.r == null then {} else x.r.bst_repr));

        Br' := r.Set_l(Br', null);
        Br' := r.Set_p(Br', x.p);
        Br' := r.Set_min(Br', r.k);
        Br' := r.Set_bst_keys(Br', {r.k} + (if r.r == null then {} else r.r.bst_keys));
        Br' := r.Set_bst_repr(Br', {r} + (if r.r == null then {} else r.r.bst_repr));

        Br' := AssertLCAndRemove(Br', x);
        Br' := AssertLCAndRemove(Br', r_l);

        // Awkward change to non-ghost code.
        var fix_p_l := p.l == x;
        var fix_p_r := p.r == x;

        var tmp;
        Br', tmp, root := BSTRemoveRootInside(Br', q, x);

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
        Br' := r.Set_bst_keys(
            Br', 
            (if r.l == null then {} else r.l.bst_keys)
            + {r.k} + (if r.r == null then {} else r.r.bst_keys)
        );
        Br' := r.Set_bst_repr(
            Br', 
            (if r.l == null then {} else r.l.bst_repr)
            + {r} + (if r.r == null then {} else r.r.bst_repr)
        );
        Br' := r.Set_bst_depth(Br', 1 + r.p.bst_depth);
        
        IfNotBrList_ThenList_LC(Br', r.l);
        Br' := BSTFixDepth(Br', q, r.l);
        if r.r != null {
            IfNotBrList_ThenList_LC(Br', r.r);
            Br' := BSTFixDepth(Br', q, r.r);
        }
        IfNotBrList_ThenList_LC(Br', r.l);
        Br' := AssertLCAndRemove(Br', r.l);
        Br' := AssertLCAndRemove(Br', r.r);
        IfNotBrList_ThenList_LC(Br', r);
        Br' := AssertLCAndRemove(Br', r);
    
        ret := r;
    }
}

