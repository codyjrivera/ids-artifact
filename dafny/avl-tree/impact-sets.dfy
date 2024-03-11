// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions"
// by Anonymous Authors.
// 
// Artifact by Anonymous Author, 2023-2024. 
//
// Impact set verification for AVL trees.

include "avl-tree.dfy"

method Check_Create(k: int, arb: AVLNode)
{
    assume arb.LC();
    var node := new AVLNode(k);
    // Note that arb cannot be node anyway
    assert arb.LC();
}

method Check_Set_k(x: AVLNode, k: int, arb: AVLNode)
    modifies x
{
    assume arb.LC();
    assume arb != x.p;
    assume arb != x;
    x.k := k;
    assert arb.LC();
}

method Check_Set_l(x: AVLNode, l: AVLNode?, arb: AVLNode)
    modifies x
{
    assume arb.LC();
    assume arb != x.l;
    assume arb != x;
    x.l := l;
    assert arb.LC();
}

method Check_Set_r(x: AVLNode, r: AVLNode?, arb: AVLNode)
    modifies x
{
    assume arb.LC();
    assume arb != x.r;
    assume arb != x;
    x.r := r;
    assert arb.LC();
}

method Check_Set_p(x: AVLNode, p: AVLNode?, arb: AVLNode)
    modifies x
{
    assume arb.LC();
    assume arb != x.p;
    assume arb != x;
    x.p := p;
    assert arb.LC();
}

method Check_Set_min(x: AVLNode, min: int, arb: AVLNode)
    modifies x
{
    assume arb.LC();
    assume arb != x.p;
    assume arb != x;
    x.min := min;
    assert arb.LC();
}

method Check_Set_max(x: AVLNode, max: int, arb: AVLNode)
    modifies x
{
    assume arb.LC();
    assume arb != x.p;
    assume arb != x;
    x.max := max;
    assert arb.LC();
}

method Check_Set_keys(x: AVLNode, keys: set<int>, arb: AVLNode)
    modifies x
{
    assume arb.LC();
    assume arb != x.p;
    assume arb != x;
    x.keys := keys;
    assert arb.LC();
}

method Check_Set_repr(x: AVLNode, repr: set<AVLNode>, arb: AVLNode)
    modifies x
{
    assume arb.LC();
    assume arb != x.p;
    assume arb != x;
    x.repr := repr;
    assert arb.LC();
}

method Check_Set_height(x: AVLNode, height: nat, arb: AVLNode)
    modifies x
{
    assume arb.LC();
    assume arb != x.p;
    assume arb != x;
    x.height := height;
    assert arb.LC();
}
