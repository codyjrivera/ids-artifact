// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions"
// by Anonymous Authors.
// 
// Artifact by Anonymous Author, 2023-2024. 
//
// Verification of Circular List Insert Front.

include "circular-list.dfy"

/**
 * Insert at the front of a circular list.
 * 
 * -> [x: last] -> [x.next] ->
 *          ==>
 * -> [x: last] -> [new node] -> [x.next] ->
 */
method CircularInsertFront(ghost Br: set<CircularNode>, x: CircularNode, k: int)
    returns (ghost Br': set<CircularNode>)
    requires Br == {}
    requires x.LC() && x.last == x
    modifies x.last.repr
    ensures x.LC() && x.last == x
    ensures x.last.keys == old(x.last.keys) + {k}
    ensures fresh(x.last.repr - old(x.last.repr))
    ensures Br' == {}
{
    Br' := Br;

    IfNotBr_ThenLC(Br', x.next);

    var node;
    Br', node := CircularNode.Create(Br', k);
    Br' := node.Set_next(Br', x.next);
    Br' := x.Set_next(Br', node);

    // Repairing 'node'
    Br' := node.Set_last(Br', x);
    Br' := node.Set_rlen(Br', 1);
    Br' := node.Set_len(Br', node.next.len + 1);
    Br' := node.Set_keys(Br', {node.k} + (if node.next == x then {} else node.next.keys));
    Br' := node.Set_repr(Br', {node} + (if node.next == x then {} else node.next.repr));
    Br' := node.next.Set_prev(Br', node);

    // Repairing 'x'
    if x.prev == x {
        Br' := x.Set_prev(Br', node);
    }
    Br' := node.Set_prev(Br', x);
    Br' := x.AddToLastRepr(Br', node);
    Br' := x.AddToLastKeys(Br', k);

    Br' := AssertLCAndRemove(Br', x);
    Br' := AssertLCAndRemove(Br', node);

    assert Br' <= {node.next};

    // Repairing 'node.next' and its descendants
    ghost var cur := node.next;
    label PreLoop1:
    while cur != x
        invariant cur != x ==> (
            Br' == {cur}
            && cur.LC_Trans_NoRlen() 
            && cur.last == x
            && cur.len > 0 
        )
        invariant cur == x ==> (
            cur.LC()
            && cur.last == x
        )
        invariant unchanged@PreLoop1(x)
        invariant Br' <= {cur}
        decreases cur.len
    {
        IfNotBr_ThenLC(Br', cur.next);
        Br' := cur.Set_rlen(Br', cur.prev.rlen + 1);
        Br' := AssertLCAndRemove(Br', cur);
        cur := cur.next;
    }
    Br' := AssertLCAndRemove(Br', cur);
}
