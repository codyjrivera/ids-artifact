// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions"
// by Adithya Murali, Cody Rivera, and P. Madhusudan.
// 
// Artifact by Cody Rivera, 2023-2024. 
//
// Verification of SLL Insert.

include "single-linked-list.dfy"

method SLLInsert(ghost Br: set<SLLNode>, x: SLLNode?, k: int)
    returns (ghost Br': set<SLLNode>, ret: SLLNode)
    requires Br == {}
    requires x != null ==> x.LC()
    modifies if x == null then {} else x.repr
    decreases if x == null then {} else x.repr
    ensures ret.LC()
    ensures ret.keys == (if x == null then {} else old(x.keys)) + {k}
    ensures fresh(ret.repr - (if x == null then {} else old(x.repr)))
    ensures ret.prev == null
    ensures x != null ==> ret == x || ret.next == x
    ensures x == null || old(x.prev) == null ==> Br' == {}
    ensures x != null && old(x.prev) != null ==> Br' == {old(x.prev)}
{
    Br' := Br;
    if x == null {
        var node;
        Br', node := SLLNode.Create(Br', k);
        Br' := node.Set_keys(Br', {k});
        Br' := node.Set_repr(Br', {node});
        Br' := AssertLCAndRemove(Br', node);
        ret := node;
    } else if k <= x.k {
        var node;
        Br', node := SLLNode.Create(Br', k);
        Br' := node.Set_next(Br', x);
        Br' := x.Set_prev(Br', node);
        Br' := node.Set_keys(Br', {node.k} + (if node.next == null then {} else node.next.keys));
        Br' := node.Set_repr(Br', {node} + (if node.next == null then {} else node.next.repr));
        Br' := AssertLCAndRemove(Br', x);
        Br' := AssertLCAndRemove(Br', node);
        ret := node;
    } else {
        if x.next != null {
            IfNotBr_ThenLC(Br', x.next);
        }
        var tmp;
        Br', tmp := SLLInsert(Br', x.next, k);
        if x.next != null {
            IfNotBr_ThenLC(Br', x.next);
        }
        var oldnext := x.next;
        Br' := tmp.Set_prev(Br', x);
        Br' := x.Set_next(Br', tmp);
        Br' := AssertLCAndRemove(Br', tmp);
        Br' := AssertLCAndRemove(Br', oldnext);
        Br' := x.Set_keys(Br', {x.k} + (if x.next == null then {} else x.next.keys));
        Br' := x.Set_repr(Br', {x} + (if x.next == null then {} else x.next.repr));
        Br' := x.Set_prev(Br', null);
        Br' := AssertLCAndRemove(Br', x);
        ret := x;
    }
}
