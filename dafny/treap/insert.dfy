// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions"
// by Anonymous Authors.
// 
// Artifact by Anonymous Author, 2023-2024. 
//
// Verification of Treap Insert.

include "treap.dfy"

method TreapInsert(ghost Br: set<TreapNode>, x: TreapNode?, k: int, prio: int)
    returns (ghost Br': set<TreapNode>, ret: TreapNode)
    requires Br == {}
    requires x != null ==> (
        x.LC()
        && k !in x.keys
    )
    modifies if x == null then {} else x.repr
    decreases if x == null then {} else x.repr
    ensures ret.LC()
    ensures ret.p == null
    ensures x != null ==> (ret == x || ret.l == x || ret.r == x)
    ensures (x == null ==>
                ret.keys == {k}
                && ret.min == k == ret.max
                && fresh(ret.repr)
                && Br' == {})
    ensures (x != null ==>
                ret.keys == old(x.keys) + {k}
                && (ret.min == old(x.min) || ret.min == k)
                && (ret.max == old(x.max) || ret.max == k)
                && (ret.l != null ==> ret.l.prio <= old(x.prio))
                && (ret.r != null ==> ret.r.prio <= old(x.prio))
                && fresh(ret.repr - old(x.repr))
                && (old(x.p) == null ==> Br' == {})
                && (old(x.p) != null ==> 
                        Br' == {old(x.p)}))
{
    Br' := Br;
    if (x == null) {
        var leaf;
        Br', leaf := TreapNode.Create(Br', k, prio);
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
        Br', tmp := TreapInsert(Br', x.l, k, prio);

        if tmp.prio <= x.prio {
            if (x.l != null) {
                IfNotBr_ThenLC(Br', x.l);
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
            if tmp.l != null {
                IfNotBr_ThenLC(Br', tmp.l);
            }
            if tmp.r != null {
                IfNotBr_ThenLC(Br', tmp.r);
            }
            var lr := tmp.r;

            Br' := x.Set_l(Br', lr);
            Br' := AssertLCAndRemove(Br', old(x.l));
            if lr != null {
                Br' := lr.Set_p(Br', x);
            }
            Br' := x.Set_min(Br', if x.l == null then x.k else x.l.min);
            Br' := x.Set_max(Br', if x.r == null then x.k else x.r.max);
            Br' := x.Set_keys(Br', (if x.l == null then {} else x.l.keys) 
                                    + {x.k} + (if x.r == null then {} else x.r.keys));
            Br' := x.Set_repr(Br', (if x.l == null then {} else x.l.repr) 
                                    + {x} + (if x.r == null then {} else x.r.repr));

            Br' := tmp.Set_r(Br', x);
            Br' := x.Set_p(Br', tmp);
            Br' := tmp.Set_min(Br', if tmp.l == null then tmp.k else tmp.l.min);
            Br' := tmp.Set_max(Br', if tmp.r == null then tmp.k else tmp.r.max);
            Br' := tmp.Set_keys(Br', (if tmp.l == null then {} else tmp.l.keys) 
                                    + {tmp.k} + (if tmp.r == null then {} else tmp.r.keys));
            Br' := tmp.Set_repr(Br', (if tmp.l == null then {} else tmp.l.repr) 
                                    + {tmp} + (if tmp.r == null then {} else tmp.r.repr));

            Br' := AssertLCAndRemove(Br', lr);
            Br' := AssertLCAndRemove(Br', x);
            Br' := AssertLCAndRemove(Br', tmp);

            ret := tmp;
        }
    } else {
        if (x.l != null) {
            IfNotBr_ThenLC(Br', x.l);
        }
        if (x.r != null) {
            IfNotBr_ThenLC(Br', x.r);
        }
        var tmp;
        Br', tmp := TreapInsert(Br', x.r, k, prio);

        if tmp.prio <= x.prio {
            if (x.r != null) {
                IfNotBr_ThenLC(Br', x.r);
            }

            ghost var oldr := x.r;
            Br' := x.Set_r(Br', tmp);
            Br' := tmp.Set_p(Br', x);

            Br' := x.Set_min(Br', if x.l == null then x.k else x.l.min);
            Br' := x.Set_max(Br', if x.r == null then x.k else x.r.max);
            Br' := x.Set_keys(Br', x.r.keys + {x.k} + (if x.l == null then {} else x.l.keys));
            Br' := x.Set_repr(Br', x.r.repr + {x} + (if x.l == null then {} else x.l.repr));
            Br' := x.Set_p(Br', null);

            Br' := AssertLCAndRemove(Br', tmp);
            Br' := AssertLCAndRemove(Br', x);
            Br' := AssertLCAndRemove(Br', oldr);

            ret := x;
        } else {
            if tmp.l != null {
                IfNotBr_ThenLC(Br', tmp.l);
            }
            if tmp.r != null {
                IfNotBr_ThenLC(Br', tmp.r);
            }
            var rl := tmp.l;

            Br' := x.Set_r(Br', rl);
            Br' := AssertLCAndRemove(Br', old(x.r));
            if rl != null {
                Br' := rl.Set_p(Br', x);
            }
            Br' := x.Set_min(Br', if x.l == null then x.k else x.l.min);
            Br' := x.Set_max(Br', if x.r == null then x.k else x.r.max);
            Br' := x.Set_keys(Br', (if x.l == null then {} else x.l.keys) 
                                    + {x.k} + (if x.r == null then {} else x.r.keys));
            Br' := x.Set_repr(Br', (if x.l == null then {} else x.l.repr) 
                                    + {x} + (if x.r == null then {} else x.r.repr));

            Br' := tmp.Set_l(Br', x);
            Br' := x.Set_p(Br', tmp);
            Br' := tmp.Set_min(Br', if tmp.l == null then tmp.k else tmp.l.min);
            Br' := tmp.Set_max(Br', if tmp.r == null then tmp.k else tmp.r.max);
            Br' := tmp.Set_keys(Br', (if tmp.l == null then {} else tmp.l.keys) 
                                    + {tmp.k} + (if tmp.r == null then {} else tmp.r.keys));
            Br' := tmp.Set_repr(Br', (if tmp.l == null then {} else tmp.l.repr) 
                                    + {tmp} + (if tmp.r == null then {} else tmp.r.repr));

            Br' := AssertLCAndRemove(Br', rl);
            Br' := AssertLCAndRemove(Br', x);
            Br' := AssertLCAndRemove(Br', tmp);

            ret := tmp;
        }
    }
}

