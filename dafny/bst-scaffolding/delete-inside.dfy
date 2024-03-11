// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions"
// by Anonymous Authors.
// 
// Artifact by Anonymous Author, 2023. 
//
// Verification of BST+Scaffolding Delete Inside.

include "bst-scaffolding.dfy"

ghost method {:extern} BSTFixDepth(Br: set<BSTNode>, x: BSTNode)
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

/**
 * BST remove root.
 */
method {:extern} BSTRemoveRootInside(ghost Br: set<BSTNode>, x: BSTNode)
    returns (ghost Br': set<BSTNode>, ret: BSTNode?, root: BSTNode)
    requires x.repr !! Br
    requires x.LC() && x.p != null
    requires x.p.l == x || x.p.r == x
    requires !(x.p.l == x && x.p.r == x)
    modifies x.repr * x.root.repr, x.p
    decreases x.repr
    ensures ret == null || ret == old(x.l) || ret == old(x.r)
    ensures (old(x.repr) == {x} ==> ret == null)
    ensures (old(x.repr) > {x} ==> ret != null)
    ensures (ret != null ==> 
                ret.LC()
                && ret.keys == old(x.keys) - {x.k}
                && ret.min >= old(x.min)
                && ret.max <= old(x.max)
                && ret.repr == old(x.repr) - {x}
                && ret.root == old(x.root)
                && ret.p == old(x.p))
    ensures old(x.p.l) == x ==> old(x.p).l == ret
    ensures old(x.p.l) != x ==> old(x.p).l == old(x.p.l)
    ensures old(x.p.r) == x ==> old(x.p).r == ret
    ensures old(x.p.r) != x ==> old(x.p).r == old(x.p.r)
    ensures old(x.p.k) == old(x.p).k
    ensures old(x.p.p) == old(x.p).p
    ensures old(x.p.keys) == old(x.p).keys
    ensures old(x.p.repr) == old(x.p).repr
    ensures old(x.p.min) == old(x.p).min
    ensures old(x.p.max) == old(x.p).max
    ensures old(x.p.depth) == old(x.p).depth
    ensures old(x.p.root) == old(x.p).root
    ensures root == x && root.k == old(x.k)
    ensures root.LC() && root.Isolated()
    ensures old(x.p) == null ==> Br' == Br 
    ensures old(x.p) != null ==> Br' == Br + {old(x.p)}

method BSTDeleteInside(ghost Br: set<BSTNode>, ghost root: BSTNode, x: BSTNode)
    returns (ghost Br': set<BSTNode>, ret: BSTNode?, node: BSTNode)
    requires Br == {}
    requires x.LC() && x.p != null
    requires x.p.l == x || x.p.r == x
    requires !(x.p.l == x && x.p.r == x)
    requires x.root == root
    modifies x.root.repr
    ensures ret == null || ret == old(x.l) || ret == old(x.r)
    ensures (old(x.repr) == {x} ==> ret == null)
    ensures (old(x.repr) > {x} ==> ret != null)
    ensures (ret != null ==> 
                ret.LC()
                && ret.keys == old(x.keys) - {x.k}
                && ret.min >= old(x.min)
                && ret.max <= old(x.max)
                && ret.repr == old(x.repr) - {x}
                && ret.root == root
                && ret.p == old(x.p))
    ensures root.keys == old(root.keys) - {x.k}
    ensures root.min >= old(root.min)
    ensures root.max >= old(root.max)
    ensures root.repr == old(root.repr) - {x}
    ensures root.root == old(root.root)
    ensures root.p == old(root.p)
    ensures node == x && node.k == old(x.k)
    ensures node.LC() && node.Isolated()
    ensures Br' == {}
{
    Br' := Br;
    var p := x.p;
    IfNotBr_ThenLC(Br', p);
    if p.l != null {
        IfNotBr_ThenLC(Br', p.l);
    }
    if p.r != null {
        IfNotBr_ThenLC(Br', p.r);
    }
    Br', ret, node := BSTRemoveRootInside(Br', x);
    ghost var cur := p;

    label PreLoop0:
    while cur.p != null
        invariant Br' == {cur}
        invariant cur.LC_Trans_PlusNode(node)
        invariant node.k in cur.keys
        invariant cur.p != null && cur.l != null ==> (
            node !in cur.l.repr 
            && node.k !in cur.l.keys
            && cur.min <= cur.l.min
            && cur.l.max < cur.k
        )
        invariant cur.p != null && cur.r != null ==> (
            node !in cur.r.repr 
            && node.k !in cur.r.keys
            && cur.k < cur.r.min
            && cur.r.max <= cur.max
        )
        invariant cur.p == null && cur.r != null ==> (
            node !in cur.r.repr
            && node.k !in cur.r.keys
        )
        invariant cur in root.repr
        invariant cur.root == root
        invariant cur.p != null ==> cur.k != node.k
        invariant unchanged@PreLoop0(root)
        invariant unchanged@PreLoop0(node)
        invariant ret != null ==> unchanged@PreLoop0(ret)
        decreases cur.depth
    {
        IfNotBr_ThenLC(Br', cur.p);
        if cur.l != null {
            IfNotBr_ThenLC(Br', cur.l);
        }
        if cur.r != null {
            IfNotBr_ThenLC(Br', cur.r);
        }
        Br' := cur.Set_repr(Br', (if cur.l == null then {} else cur.l.repr)
                                + {cur}
                                + (if cur.r == null then {} else cur.r.repr));
        Br' := cur.Set_keys(Br', (if cur.l == null then {} else cur.l.keys)
                                + {cur.k}
                                + (if cur.r == null then {} else cur.r.keys));
        Br' := cur.Set_min(Br', if cur.l == null then cur.k else cur.l.min);
        Br' := cur.Set_max(Br', if cur.r == null then cur.k else cur.r.max);
        Br' := AssertLCAndRemove(Br', cur);
        cur := cur.p;
    }

    Br' := cur.DeleteFromRootRepr(Br', node);
    Br' := cur.Set_keys(Br', (if cur.r == null then {} else cur.r.keys));
    Br' := AssertLCAndRemove(Br', cur);

    if ret != null {
        IfNotBr_ThenLC(Br', ret);
    }
}