// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions"
// by Adithya Murali, Cody Rivera, and P. Madhusudan.
// 
// Artifact by Cody Rivera, 2023-2024. 
//
// Impact set verification for circular lists.

include "circular-list.dfy"

method Check_Create(k: int, arb: CircularNode)
{
    assume arb.LC();
    var node := new CircularNode(k);
    assert arb.LC();
}

method Check_Set_k(x: CircularNode, k: int, arb: CircularNode)
    modifies x
{
    assume arb.LC();
    assume arb != x.prev;
    assume arb != x;
    x.k := k;
    assert arb.LC();
}

method Check_Set_next(x: CircularNode, next: CircularNode, arb: CircularNode)
    modifies x
{
    assume arb.LC();
    assume arb != x.next;
    assume arb != x;
    x.next := next;
    assert arb.LC();
}

method Check_Set_prev(x: CircularNode, prev: CircularNode, arb: CircularNode)
    modifies x
{
    assume arb.LC();
    assume arb != x.prev;
    assume arb != x;
    x.prev := prev;
    assert arb.LC();
}

method Check_Set_last(x: CircularNode, last: CircularNode, arb: CircularNode)
    modifies x
{
    assume arb.LC();
    assume x.last != x || (x.last == x && x.repr == {x});
    assume arb != x.prev;
    assume arb != x;
    x.last := last;
    assert arb.LC();
}

method Check_Set_len(x: CircularNode, len: nat, arb: CircularNode)
    modifies x
{
    assume arb.LC();
    assume arb != x.prev;
    assume arb != x;
    x.len := len;
    assert arb.LC();
}

method Check_Set_rlen(x: CircularNode, rlen: nat, arb: CircularNode)
    modifies x
{
    assume arb.LC();
    assume arb != x.next;
    assume arb != x;
    x.rlen := rlen;
    assert arb.LC();
}

method Check_Set_keys(x: CircularNode, keys: set<int>, arb: CircularNode)
    modifies x
{
    assume arb.LC();
    assume arb != x.prev;
    assume arb != x;
    x.keys := keys;
    assert arb.LC();
}


method Check_Set_repr(x: CircularNode, repr: set<CircularNode>, arb: CircularNode)
    modifies x
{
    assume arb.LC();
    assume x.last != x || (x.last == x && x.repr == {x});
    assume arb != x.prev;
    assume arb != x;
    x.repr := repr;
    assert arb.LC();
}

method Check_AddToLastRepr(x: CircularNode, node: CircularNode, arb: CircularNode)
    modifies x
{
    assume arb.LC();
    assume x.last == x;
    assume arb != x;
    x.repr := x.repr + {node};
    assert arb.LC();
}

method Check_AddToLastKeys(x: CircularNode, k: int, arb: CircularNode)
    modifies x
{
    assume arb.LC();
    assume x.last == x;
    assume arb != x;
    x.keys := x.keys + {k};
    assert arb.LC();
}

method Check_DeleteFromLastRepr(x: CircularNode, node: CircularNode, arb: CircularNode)
    modifies x
{
    assume arb.LC();
    assume x.last == x && node.next == node && node.prev == node;
    assume arb != x;
    x.repr := x.repr - {node};
    assert arb.LC();
}

method Check_DeleteFromLastKeys(x: CircularNode, k: int, arb: CircularNode)
    modifies x
{
    assume arb.LC();
    assume x.last == x;
    assume arb != x;
    x.keys := x.keys - {k};
    assert arb.LC();
}