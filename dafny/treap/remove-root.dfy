// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions"
// by Anonymous Authors.
// 
// Artifact by Anonymous Author, 2023. 
//
// Verification of Treap Remove Root.

include "treap.dfy"

function MaxReal(x: int, y: int): int {
    if x > y then x else y
}

method TreapRemoveRoot(ghost Br: set<TreapNode>, x: TreapNode)
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
        //TreapNotIn_Keyset(Br, r, x.k);

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
        //TreapNotIn_Keyset(Br, l, x.k);

        ret := l; root := x;
    } else {
        if x.l.prio <= x.r.prio {
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
            //TreapNotIn_Keyset(Br, r, x.k);

            var tmp;
            Br', tmp, root := TreapRemoveRoot(Br', x);

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
        } else {
            IfNotBr_ThenLC(Br', x.l);
            IfNotBr_ThenLC(Br', x.r);
            if (x.l.l != null) {
                IfNotBr_ThenLC(Br', x.l.l);
            }
            if (x.l.r != null) {
                IfNotBr_ThenLC(Br', x.l.r);
            }

            var l := x.l;
            var l_r := l.r;

            Br' := x.Set_l(Br', l_r);
            if (l_r != null) {
                Br' := l_r.Set_p(Br', x);
            }
            Br' := x.Set_min(Br', if x.l == null then x.k else x.l.min);
            Br' := x.Set_keys(Br', x.r.keys + {x.k} + (if x.l == null then {} else x.l.keys));
            Br' := x.Set_repr(Br', x.r.repr + {x} + (if x.l == null then {} else x.l.repr));

            Br' := l.Set_r(Br', null);
            Br' := l.Set_p(Br', null);
            Br' := l.Set_max(Br', l.k);
            Br' := l.Set_keys(Br', {l.k} + (if l.l == null then {} else l.l.keys));
            Br' := l.Set_repr(Br', {l} + (if l.l == null then {} else l.l.repr));

            Br' := AssertLCAndRemove(Br', x);
            Br' := AssertLCAndRemove(Br', l_r);
            Br' := AssertLCAndRemove(Br', l);
            //TreapNotIn_Keyset(Br, r, x.k);

            var tmp;
            Br', tmp, root := TreapRemoveRoot(Br', x);

            Br' := l.Set_r(Br', tmp);
            if (tmp != null) {
                Br' := tmp.Set_p(Br', l);
            }
            Br' := l.Set_p(Br', null);
            Br' := l.Set_max(Br', if l.r == null then l.k else l.r.max);
            Br' := l.Set_keys(
                Br', 
                (if l.r == null then {} else l.r.keys)
                + {l.k} + (if l.l == null then {} else l.l.keys)
            );
            Br' := l.Set_repr(
                Br', 
                (if l.r == null then {} else l.r.repr)
                + {l} + (if l.l == null then {} else l.l.repr)
            );
            Br' := AssertLCAndRemove(Br', l);
            Br' := AssertLCAndRemove(Br', l.r);

            ret := l;
        }
    }
}
