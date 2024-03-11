// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions"
// by Anonymous Authors.
// 
// Artifact by Anonymous Author, 2023-2024. 
//
// Verification of Treap Insert.

include "treap.dfy"

function MaxReal(x: int, y: int): int {
    if x > y then x else y
}

method {:extern} TreapRemoveRoot(ghost Br: set<TreapNode>, x: TreapNode)
    returns (ghost Br': set<TreapNode>, ret: TreapNode?, root: TreapNode)
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
                && ret.repr <= old(x.repr)
                && (old(x.l) != null && old(x.r) == null ==>
                        ret.prio == old(x.l.prio))
                && (old(x.l) == null && old(x.r) != null ==>
                        ret.prio == old(x.r.prio))
                && (old(x.l) != null && old(x.r) != null ==>
                        ret.prio <= MaxReal(old(x.l.prio), old(x.r.prio))))
    ensures root == x && root.k == old(x.k)
    ensures root.LC() && root.Isolated()
    ensures old(x.p) == null ==> Br' == Br 
    ensures old(x.p) != null ==> Br' == Br + {old(x.p)}

method TreapDelete(ghost Br: set<TreapNode>, x: TreapNode, k: int)
    returns (ghost Br': set<TreapNode>, ret: TreapNode?, del: TreapNode?)
    requires Br == {}
    requires x.LC() //&& k in x.keys
    modifies x.repr
    decreases x.repr
    ensures ret == null || ret == x || ret == old(x.l) || ret == old(x.r)
    ensures x.p == null
    //ensures (old(x.keys) == {k} ==> ret == null)
    //ensures (old(x.keys) > {k} ==> ret != null)
    ensures (ret == null ==> old(x.keys) == {k} && del != null)
    ensures (ret != null ==> 
                ret.LC()
                && ret.p == null
                && (del != null ==> 
                        ret.keys == old(x.keys) - {k}
                        && ret.min >= old(x.min)
                        && ret.max <= old(x.max)
                        && ret.repr <= old(x.repr)
                        && ret.prio <= old(x.prio))
                && (del == null ==> 
                        ret.keys == old(x.keys)
                        && ret.min == old(x.min)
                        && ret.max == old(x.max)
                        && ret.repr == old(x.repr)
                        && ret.prio == old(x.prio)))
    ensures del != null ==> del.k == k && k in old(x.keys)
    ensures del != null ==> del.LC() && del.Isolated()
    ensures old(x.p) == null ==> Br' == Br 
    ensures old(x.p) != null ==> Br' == Br + {old(x.p)}
{
    Br' := Br;
    if (x.k == k) {
        Br', ret, del := TreapRemoveRoot(Br', x);
    } else if (k < x.k && x.l != null) {
        if (x.l != null) {
            IfNotBr_ThenLC(Br', x.l);
        }
        if (x.r != null) {
            IfNotBr_ThenLC(Br', x.r);
        }
        if (x.r != null) {
            //TreapNotIn_Keyset(Br', x.r, k);
        }
        var l;
        Br', l, del := TreapDelete(Br', x.l, k);
        if (x.l != null) {
            IfNotBr_ThenLC(Br', x.l);
        }
        Br' := x.Set_l(Br', l);
        if (l != null) {
            Br' := l.Set_p(Br', x);
        }
        Br' := x.Set_p(Br', null);
        Br' := x.Set_min(Br', if x.l == null then x.k else x.l.min);
        Br' := x.Set_keys(
            Br', 
            (if x.l == null then {} else x.l.keys)
            + {x.k} + (if x.r == null then {} else x.r.keys)
        );
        Br' := x.Set_repr(
            Br', 
            (if x.l == null then {} else x.l.repr)
            + {x} + (if x.r == null then {} else x.r.repr)
        );
        Br' := AssertLCAndRemove(Br', x);
        Br' := AssertLCAndRemove(Br', l);
        Br' := AssertLCAndRemove(Br', old(x.l));
        ret := x;
    } else if (k > x.k && x.r != null) {
        if (x.l != null) {
            IfNotBr_ThenLC(Br', x.l);
        }
        if (x.r != null) {
            IfNotBr_ThenLC(Br', x.r);
        }
        if (x.l != null) {
            //TreapNotIn_Keyset(Br', x.l, k);
        }
        var r;
        Br', r, del := TreapDelete(Br', x.r, k);
        if (x.r != null) {
            IfNotBr_ThenLC(Br', x.r);
        }
        Br' := x.Set_r(Br', r);
        if (r != null) {
            Br' := r.Set_p(Br', x);
        }
        Br' := x.Set_p(Br', null);
        Br' := x.Set_max(Br', if x.r == null then x.k else x.r.max);
        Br' := x.Set_keys(
            Br', 
            (if x.l == null then {} else x.l.keys)
            + {x.k} + (if x.r == null then {} else x.r.keys)
        );
        Br' := x.Set_repr(
            Br', 
            (if x.l == null then {} else x.l.repr)
            + {x} + (if x.r == null then {} else x.r.repr)
        );
        Br' := AssertLCAndRemove(Br', x);
        Br' := AssertLCAndRemove(Br', r);
        Br' := AssertLCAndRemove(Br', old(x.r));
        ret := x;
    } else {
        Br' := x.Set_p(Br', null);
        Br' := AssertLCAndRemove(Br', x);
        ret, del := x, null;
    }
}