// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions"
// by Anonymous Authors.
// 
// Artifact by Anonymous Author, 2023-2024. 
//
// Verification of Circular List Insert Back.

include "circular-list.dfy"

/**
 * Insert at the back of a circular list (before the scaffolding node 'last').
 * 
 * -> [x] -> [x.next: last] ->
 *          ==>
 * -> [x] -> [new node] -> [x.next: last] ->
 * (return value 'ret' is the new node)
 */
method CircularInsertBack(ghost Br: set<CircularNode>, x: CircularNode, k: int)
    returns (ghost Br': set<CircularNode>,
             ret: CircularNode)
    requires Br == {}
    requires x.LC() && x.next == x.last
    modifies x.last.repr
    ensures ret.LC() && ret.next == ret.last
    ensures ret.last == old(x.last)
    ensures ret.last.keys == old(x.last.keys) + {k}
    ensures fresh(ret.last.repr - old(x.last.repr))
    ensures Br' == {}
{
    Br' := Br;

    IfNotBr_ThenLC(Br', x.prev);
    IfNotBr_ThenLC(Br', x.next);

    var last := x.next;

    var node;
    Br', node := CircularNode.Create(Br', k);
    Br' := node.Set_next(Br', x.next);
    Br' := x.Set_next(Br', node);

    // Updating ghost fields of Last
    Br' := last.AddToLastRepr(Br', node);
    Br' := last.Set_prev(Br', node);

    // Repairing 'node'
    Br' := node.Set_prev(Br', x);
    Br' := node.Set_len(Br', 1);
    Br' := node.Set_rlen(Br', 1 + node.prev.rlen);
    Br' := node.Set_keys(Br', {k});
    Br' := node.Set_repr(Br', {node});
    Br' := node.Set_last(Br', node.prev.last);
    Br' := AssertLCAndRemove(Br', node);

    assert Br' == {node.prev, last};

    ghost var cur := x;
    label PreLoop1:
    while cur != last
        invariant cur != last ==> (
            Br' == {cur, last}
            && cur.LC_Trans_MinusNode(node)
            && cur.last == last
            && last.LC_At_Last(node)
        )
        invariant cur == last ==> (
            cur.LC_Trans_MinusNode(node)
        )
        invariant node in cur.next.repr
        invariant k in cur.next.keys
        invariant unchanged@PreLoop1(node)
        invariant unchanged@PreLoop1(last)
        invariant Br' <= {cur, last}
        decreases cur.rlen
    {
        if cur.prev != last {
            IfNotBr_ThenLC(Br', cur.prev);
        }
        assert cur.repr == {cur} + (cur.next.repr - {node});
        Br' := cur.Set_len(Br', cur.next.len + 1);
        Br' := cur.Set_repr(Br', cur.repr + {node});
        Br' := cur.Set_keys(Br', cur.keys + {node.k});
        Br' := AssertLCAndRemove(Br', cur);
        cur := cur.prev;
    }
    IfNotBr_ThenLC(Br', node);
    Br' := cur.Set_keys(Br', cur.next.keys);
    Br' := AssertLCAndRemove(Br', cur);
    Br' := AssertLCAndRemove(Br', node);

    ret := node;
}
