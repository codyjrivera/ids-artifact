// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions"
// by Adithya Murali, Cody Rivera, and P. Madhusudan.
// 
// Artifact by Cody Rivera, 2023-2024. 
//
// Verification of Circular List Delete Front.

include "circular-list.dfy"

/**
 * Deletes from the front of a circular list.
 * 
 * -> [x: last] -> [x.next] -> [x.next.next] ->
 *          ==>
 * -> [x: last] -> [x.next.next] ->
 */
method CircularDeleteFront(ghost Br: set<CircularNode>, x: CircularNode, k: int)
    returns (ghost Br': set<CircularNode>)
    requires Br == {}
    requires x.LC() && x.last == x
    requires x.next != x
    modifies x.last.repr
    ensures x.LC() && x.last == x
    ensures x.last.keys == old(x.last.keys) || x.last.keys == old(x.last.keys) - {old(x.next.k)}
    ensures x.last.repr <= old(x.last.repr)
    ensures Br' == {}
{
    Br' := Br;

    var next := x.next;
    IfNotBr_ThenLC(Br', next);
    IfNotBr_ThenLC(Br', next.next);
    IfNotBr_ThenLC(Br', next.next.next);

    // Concrete code
    Br' := x.Set_next(Br', next.next);
    Br' := next.Set_next(Br', next);

    // Repair 'next'
    Br' := next.Set_prev(Br', next);
    Br' := next.Set_len(Br', 0);
    Br' := next.Set_rlen(Br', 0);
    Br' := next.Set_keys(Br', {});
    Br' := next.Set_repr(Br', {next});
    Br' := next.Set_last(Br', next);

    // Repair 'x'
    Br' := x.next.Set_prev(Br', x);
    Br' := x.DeleteFromLastRepr(Br', next);
    if (next.k !in x.next.keys || x.next == x) {
        Br' := x.DeleteFromLastKeys(Br', next.k);
    }

    Br' := AssertLCAndRemove(Br', next);
    Br' := AssertLCAndRemove(Br', x);

    // Repairing 'node.next' and its descendants
    ghost var cur := x.next;
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
