// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions"
// by Adithya Murali, Cody Rivera, and P. Madhusudan.
// 
// Artifact by Cody Rivera, 2023-2024. 
//
// Impact set verification for Treaps.

include "treap.dfy"

method Check_Create(k: int, prio: int, arb: TreapNode)
{
    assume arb.LC();
    var node := new TreapNode(k, prio);
    // Note that arb cannot be node anyway
    assert arb.LC();
}

method Check_Set_k(x: TreapNode, k: int, arb: TreapNode)
    modifies x
{
    assume arb.LC();
    assume arb != x.p;
    assume arb != x;
    x.k := k;
    assert arb.LC();
}

method Check_Set_prio(x: TreapNode, prio: int, arb: TreapNode)
    modifies x
{
    assume arb.LC();
    assume arb != x.p;
    assume arb != x;
    x.prio := prio;
    assert arb.LC();
}

method Check_Set_l(x: TreapNode, l: TreapNode?, arb: TreapNode)
    modifies x
{
    assume arb.LC();
    assume arb != x.l;
    assume arb != x;
    x.l := l;
    assert arb.LC();
}

method Check_Set_r(x: TreapNode, r: TreapNode?, arb: TreapNode)
    modifies x
{
    assume arb.LC();
    assume arb != x.r;
    assume arb != x;
    x.r := r;
    assert arb.LC();
}

method Check_Set_p(x: TreapNode, p: TreapNode?, arb: TreapNode)
    modifies x
{
    assume arb.LC();
    assume arb != x.p;
    assume arb != x;
    x.p := p;
    assert arb.LC();
}

method Check_Set_min(x: TreapNode, min: int, arb: TreapNode)
    modifies x
{
    assume arb.LC();
    assume arb != x.p;
    assume arb != x;
    x.min := min;
    assert arb.LC();
}

method Check_Set_max(x: TreapNode, max: int, arb: TreapNode)
    modifies x
{
    assume arb.LC();
    assume arb != x.p;
    assume arb != x;
    x.max := max;
    assert arb.LC();
}

method Check_Set_keys(x: TreapNode, keys: set<int>, arb: TreapNode)
    modifies x
{
    assume arb.LC();
    assume arb != x.p;
    assume arb != x;
    x.keys := keys;
    assert arb.LC();
}

method Check_Set_repr(x: TreapNode, repr: set<TreapNode>, arb: TreapNode)
    modifies x
{
    assume arb.LC();
    assume arb != x.p;
    assume arb != x;
    x.repr := repr;
    assert arb.LC();
}
