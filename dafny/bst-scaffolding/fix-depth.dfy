// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions"
// by Adithya Murali, Cody Rivera, and P. Madhusudan.
// 
// Artifact by Cody Rivera, 2023-2024. 
//
// Verification of BST+Scaffolding Fix Depth.

include "bst-scaffolding.dfy"

ghost method BSTFixDepth(Br: set<BSTNode>, x: BSTNode)
    returns (Br': set<BSTNode>)
    requires (x.repr - {x}) !! Br
    requires x.LC_Trans_NoDepth() && x.p != null
    modifies x.repr * x.root.repr
    decreases x.repr
    ensures x.LC()
    ensures x.k == old(x.k)
    ensures x.l == old(x.l)
    ensures x.r == old(x.r)
    ensures x.p == old(x.p)
    ensures x.min == old(x.min)
    ensures x.max == old(x.max)
    ensures x.keys == old(x.keys)
    ensures x.repr == old(x.repr)
    ensures x.root == old(x.root)
    ensures Br' == Br - {x}
{
    Br' := Br;
    if x.l != null {
        IfNotBr_ThenLC(Br', x.l);
    }
    if x.r != null {
        IfNotBr_ThenLC(Br', x.r);
    }
    Br' := x.Set_depth(Br', 1 + x.p.depth);
    Br' := AssertLCAndRemove(Br', x);

    if x.l != null {
        Br' := BSTFixDepth(Br', x.l);
    }
    if x.r != null {
        Br' := BSTFixDepth(Br', x.r);
    }
}
