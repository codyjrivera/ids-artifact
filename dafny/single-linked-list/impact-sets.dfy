// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions"
// by Adithya Murali, Cody Rivera, and P. Madhusudan.
// 
// Artifact by Cody Rivera, 2023-2024. 
//
// Impact set verification for singly-linked lists.

include "single-linked-list.dfy"

method Check_Create(k: int, arb: SLLNode)
{
    assume arb.LC();
    var node := new SLLNode(k);
    // Note that arb cannot be node anyway
    assert arb.LC();
}

method Check_Set_k(x: SLLNode, k: int, arb: SLLNode)
    modifies x
{
    assume arb.LC();
    assume arb != x.prev;
    assume arb != x;
    x.k := k;
    assert arb.LC();
}

method Check_Set_next(x: SLLNode, next: SLLNode?, arb: SLLNode)
    modifies x
{
    assume arb.LC();
    assume arb != x.next;
    assume arb != x;
    x.next := next;
    assert arb.LC();
}

method Check_Set_prev(x: SLLNode, prev: SLLNode?, arb: SLLNode)
    modifies x
{
    assume arb.LC();
    assume arb != x.prev;
    assume arb != x;
    x.prev := prev;
    assert arb.LC();
}

method Check_Set_keys(x: SLLNode, keys: set<int>, arb: SLLNode)
    modifies x
{
    assume arb.LC();
    assume arb != x.prev;
    assume arb != x;
    x.keys := keys;
    assert arb.LC();
}

method Check_Set_repr(x: SLLNode, repr: set<SLLNode>, arb: SLLNode)
    modifies x
{
    assume arb.LC();
    assume arb != x.prev;
    assume arb != x;
    x.repr := repr;
    assert arb.LC();
}

