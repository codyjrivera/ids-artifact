// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions"
// by Anonymous Authors.
// 
// Artifact by Anonymous Author, 2023. 
//
// Impact set verification for BSTs.

include "binary-search-tree.dfy"

method Check_Create(k: int, arb: BSTNode)
{
    assume arb.LC();
    var node := new BSTNode(k);
    // Note that arb cannot be node anyway
    assert arb.LC();
}

method Check_Set_k(x: BSTNode, k: int, arb: BSTNode)
    modifies x
{
    assume arb.LC();
    assume arb != x.p;
    assume arb != x;
    x.k := k;
    assert arb.LC();
}

method Check_Set_l(x: BSTNode, l: BSTNode?, arb: BSTNode)
    modifies x
{
    assume arb.LC();
    assume arb != x.l;
    assume arb != x;
    x.l := l;
    assert arb.LC();
}

method Check_Set_r(x: BSTNode, r: BSTNode?, arb: BSTNode)
    modifies x
{
    assume arb.LC();
    assume arb != x.r;
    assume arb != x;
    x.r := r;
    assert arb.LC();
}

method Check_Set_p(x: BSTNode, p: BSTNode?, arb: BSTNode)
    modifies x
{
    assume arb.LC();
    assume arb != x.p;
    assume arb != x;
    x.p := p;
    assert arb.LC();
}

method Check_Set_min(x: BSTNode, min: int, arb: BSTNode)
    modifies x
{
    assume arb.LC();
    assume arb != x.p;
    assume arb != x;
    x.min := min;
    assert arb.LC();
}

method Check_Set_max(x: BSTNode, max: int, arb: BSTNode)
    modifies x
{
    assume arb.LC();
    assume arb != x.p;
    assume arb != x;
    x.max := max;
    assert arb.LC();
}

method Check_Set_keys(x: BSTNode, keys: set<int>, arb: BSTNode)
    modifies x
{
    assume arb.LC();
    assume arb != x.p;
    assume arb != x;
    x.keys := keys;
    assert arb.LC();
}

method Check_Set_repr(x: BSTNode, repr: set<BSTNode>, arb: BSTNode)
    modifies x
{
    assume arb.LC();
    assume arb != x.p;
    assume arb != x;
    x.repr := repr;
    assert arb.LC();
}
