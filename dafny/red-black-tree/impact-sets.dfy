// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions"
// by Adithya Murali, Cody Rivera, and P. Madhusudan.
// 
// Artifact by Cody Rivera, 2023-2024. 
//
// Impact set verification for RBTs.

include "red-black-tree.dfy"

method Check_Create(k: int, arb: RBTNode)
{
    assume arb.LC();
    var node := new RBTNode(k);
    // Note that arb cannot be node anyway
    assert arb.LC();
}

method Check_Set_k(x: RBTNode, k: int, arb: RBTNode)
    modifies x
{
    assume arb.LC();
    assume arb != x.p;
    assume arb != x;
    x.k := k;
    assert arb.LC();
}

method Check_Set_l(x: RBTNode, l: RBTNode?, arb: RBTNode)
    modifies x
{
    assume arb.LC();
    assume arb != x.l;
    assume arb != x;
    x.l := l;
    assert arb.LC();
}

method Check_Set_r(x: RBTNode, r: RBTNode?, arb: RBTNode)
    modifies x
{
    assume arb.LC();
    assume arb != x.r;
    assume arb != x;
    x.r := r;
    assert arb.LC();
}

method Check_Set_p(x: RBTNode, p: RBTNode?, arb: RBTNode)
    modifies x
{
    assume arb.LC();
    assume arb != x.p;
    assume arb != x;
    x.p := p;
    assert arb.LC();
}

method Check_Set_min(x: RBTNode, min: int, arb: RBTNode)
    modifies x
{
    assume arb.LC();
    assume arb != x.p;
    assume arb != x;
    x.min := min;
    assert arb.LC();
}

method Check_Set_max(x: RBTNode, max: int, arb: RBTNode)
    modifies x
{
    assume arb.LC();
    assume arb != x.p;
    assume arb != x;
    x.max := max;
    assert arb.LC();
}

method Check_Set_keys(x: RBTNode, keys: set<int>, arb: RBTNode)
    modifies x
{
    assume arb.LC();
    assume arb != x.p;
    assume arb != x;
    x.keys := keys;
    assert arb.LC();
}

method Check_Set_repr(x: RBTNode, repr: set<RBTNode>, arb: RBTNode)
    modifies x
{
    assume arb.LC();
    assume arb != x.p;
    assume arb != x;
    x.repr := repr;
    assert arb.LC();
}

method Check_Set_black(x: RBTNode, black: bool, arb: RBTNode)
    modifies x
{
    assume arb.LC();
    assume arb != x.p;
    assume arb != x;
    x.black := black;
    assert arb.LC();
}

method Check_Set_black_height(x: RBTNode, black_height: nat, arb: RBTNode)
    modifies x
{
    assume arb.LC();
    assume arb != x.p;
    assume arb != x;
    x.black_height := black_height;
    assert arb.LC();
}
