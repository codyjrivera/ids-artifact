// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions"
// by Anonymous Authors.
// 
// Artifact by Anonymous Author, 2023. 
//
// Verification of Circular List Delete Back.

include "circular-list.dfy"

/**
 * Deletes at the back of a circular list (before the scaffolding node 'last').
 * 
 * -> [x] -> [x.next] -> [x.next.next: last] ->
 *          ==>
 * -> [x] -> [x.next.next: last] ->
 */
method CircularDeleteBack(ghost Br: set<CircularNode>, x: CircularNode)
    returns (ghost Br': set<CircularNode>)
    requires Br == {}
    requires x.LC() && x.next != x
    requires x.next.LC() && x.next.last == x.next.next
    modifies x.last.repr
    ensures x.LC() && x.next == x.last
    ensures x.last == old(x.last)
    ensures x.last.keys == old(x.last.keys) || x.last.keys == old(x.last.keys) - {old(x.next.k)}
    ensures x.last.repr <= old(x.last.repr)
    ensures Br' == {}
{
    Br' := Br;

    var next := x.next;
    var last := next.next;
    IfNotBr_ThenLC(Br', x.prev);
    IfNotBr_ThenLC(Br', next.next);

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

    // Repair 'last'
    Br' := last.Set_prev(Br', x);
    Br' := AssertLCAndRemove(Br', next);

    if (x == last) {
        // Repair the root
        Br' := x.DeleteFromLastRepr(Br', next);
        Br' := x.Set_keys(Br', {});
        Br' := AssertLCAndRemove(Br', x);
    } else {
        // Repair 'x'.
        Br' := x.Set_keys(Br', {x.k});
        Br' := x.Set_repr(Br', {x});
        Br' := x.Set_len(Br', 1);
        Br' := AssertLCAndRemove(Br', x);

        // Repair its predecessors.
        ghost var cur: CircularNode := x.prev;
        label PreLoop1:
        while cur != last
            invariant cur != last ==> (
                cur.LC_Trans_PlusNode(next)
                && last.LC()
            )
            invariant cur == last ==> (
                cur.LC_Trans_PlusNode(next)
            )
            invariant (
                cur.last == last
                && cur.next != cur.last
                && next !in cur.next.repr
            )
            invariant unchanged@PreLoop1(x)
            invariant unchanged@PreLoop1(last)
            invariant unchanged@PreLoop1(next)
            invariant Br' == {cur, last}
            decreases cur.rlen
        {
            IfNotBr_ThenLC(Br', cur.prev);
            Br' := cur.Set_keys(Br', {cur.k} + cur.next.keys);
            Br' := cur.Set_repr(Br', {cur} + cur.next.repr);
            Br' := cur.Set_len(Br', 1 + cur.next.len);
            Br' := AssertLCAndRemove(Br', cur);

            cur := cur.prev;
        }
        assert Br' == {cur};
        IfNotBr_ThenLC(Br', cur.prev);
        Br' := cur.DeleteFromLastRepr(Br', next);
        Br' := cur.Set_keys(Br', cur.next.keys);
        Br' := AssertLCAndRemove(Br', cur.prev);
        Br' := AssertLCAndRemove(Br', cur);
    }
}
