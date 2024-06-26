// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions"
// by Adithya Murali, Cody Rivera, and P. Madhusudan.
// 
// Artifact by Cody Rivera, 2023-2024. 
//
// Impact set verification for sorted lists (with min, max).

include "sorted-list-minmax.dfy"

method Check_Create(k: int, arb: SortedNode)
{
    assume arb.LC();
    var node := new SortedNode(k);
    assume arb != node;
    assert arb.LC();
}

method Check_Set_k(x: SortedNode, k: int, arb: SortedNode)
    modifies x
{
    assume arb.LC();
    assume arb != x.prev;
    assume arb != x;
    x.k := k;
    assert arb.LC();
}

method Check_Set_next(x: SortedNode, next: SortedNode?, arb: SortedNode)
    modifies x
{
    assume arb.LC();
    assume arb != x.next;
    assume arb != x;
    x.next := next;
    assert arb.LC();
}

method Check_Set_prev(x: SortedNode, prev: SortedNode?, arb: SortedNode)
    modifies x
{
    assume arb.LC();
    assume arb != x.prev;
    assume arb != x;
    x.prev := prev;
    assert arb.LC();
}

method Check_Set_keys(x: SortedNode, keys: set<int>, arb: SortedNode)
    modifies x
{
    assume arb.LC();
    assume arb != x.prev;
    assume arb != x;
    x.keys := keys;
    assert arb.LC();
}

method Check_Set_repr(x: SortedNode, repr: set<SortedNode>, arb: SortedNode)
    modifies x
{
    assume arb.LC();
    assume arb != x.prev;
    assume arb != x;
    x.repr := repr;
    assert arb.LC();
}

method Check_Set_sorted(x: SortedNode, sorted: bool, arb: SortedNode)
    modifies x
{
    assume arb.LC();
    assume arb != x.prev;
    assume arb != x;
    x.sorted := sorted;
    assert arb.LC();
}

method Check_Set_rev_sorted(x: SortedNode, rev_sorted: bool, arb: SortedNode)
    modifies x
{
    assume arb.LC();
    assume arb != x.prev;
    assume arb != x;
    x.rev_sorted := rev_sorted;
    assert arb.LC();
}

method Check_Set_min(x: SortedNode, min: int, arb: SortedNode)
    modifies x
{
    assume arb.LC();
    assume arb != x.prev;
    assume arb != x;
    x.min := min;
    assert arb.LC();
}

method Check_Set_max(x: SortedNode, max: int, arb: SortedNode)
    modifies x
{
    assume arb.LC();
    assume arb != x.prev;
    assume arb != x;
    x.max := max;
    assert arb.LC();
}
