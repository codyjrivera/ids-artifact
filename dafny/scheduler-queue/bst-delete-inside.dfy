// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions"
// by Anonymous Authors.
// 
// Artifact by Anonymous Author, 2023-2024. 
//
// Verification of Scheduler Queue Delete Inside.

include "scheduler-queue.dfy"

ghost method BSTFixDepth(Br: QueueBr, q: Queue, x: QueueNode)
    returns (Br': QueueBr)
    requires (x.bst_repr - {x}) !! Br.bst && Br.list == {}
    requires x.LC_Trans_NoDepth() && x.p != null
    modifies x.bst_repr * x.bst_root.bst_repr
    decreases x.bst_repr
    ensures x.LC()
    ensures x.k == old(x.k)
    ensures x.l == old(x.l)
    ensures x.r == old(x.r)
    ensures x.p == old(x.p)
    ensures x.min == old(x.min)
    ensures x.max == old(x.max)
    ensures x.bst_keys == old(x.bst_keys)
    ensures x.bst_repr == old(x.bst_repr)
    ensures x.bst_root == old(x.bst_root)
    ensures x.List_FieldsUnchanged()
    ensures q.q1s != null ==> q.q1s.List_FieldsUnchanged() && q.q1s.bst_root == old(q.q1s.bst_root)
    ensures Br'.bst == Br.bst - {x}
    ensures Br'.list == {}

method {:extern} BSTRemoveRootInside(ghost Br: QueueBr, q: Queue, x: QueueNode)
    returns (ghost Br': QueueBr, ret: QueueNode?, root: QueueNode)
    requires x.bst_repr !! Br.bst && Br.list == {}
    requires x.LC() && x.p != null
    requires x.p.l == x || x.p.r == x
    requires !(x.p.l == x && x.p.r == x)
    requires x.next == null && x.prev == null
    requires q.q1s != null ==> x != q.q1s
    modifies x.bst_repr * x.bst_root.bst_repr, x.p
    decreases x.bst_repr
    ensures ret == null || ret == old(x.l) || ret == old(x.r)
    ensures (old(x.bst_repr) == {x} ==> ret == null)
    ensures (old(x.bst_repr) > {x} ==> ret != null)
    ensures (ret != null ==> 
                ret.LC()
                && ret.bst_keys == old(x.bst_keys) - {x.k}
                && ret.min >= old(x.min)
                && ret.max <= old(x.max)
                && ret.bst_repr == old(x.bst_repr) - {x}
                && ret.bst_root == old(x.bst_root)
                && ret.p == old(x.p)
                && ret.List_FieldsUnchanged())
    ensures old(x.p.l) == x ==> old(x.p).l == ret
    ensures old(x.p.l) != x ==> old(x.p).l == old(x.p.l)
    ensures old(x.p.r) == x ==> old(x.p).r == ret
    ensures old(x.p.r) != x ==> old(x.p).r == old(x.p.r)
    ensures old(x.p.k) == old(x.p).k
    ensures old(x.p.p) == old(x.p).p
    ensures old(x.p.bst_keys) == old(x.p).bst_keys
    ensures old(x.p.bst_repr) == old(x.p).bst_repr
    ensures old(x.p.min) == old(x.p).min
    ensures old(x.p.max) == old(x.p).max
    ensures old(x.p.bst_depth) == old(x.p).bst_depth
    ensures old(x.p.bst_root) == old(x.p).bst_root
    ensures old(x.p).List_FieldsUnchanged()
    ensures root == x && root.k == old(x.k)
    ensures root.LC() && root.BST_Isolated()
    ensures root.List_FieldsUnchanged()
    ensures q.q1s != null ==> q.q1s.List_FieldsUnchanged() && q.q1s.bst_root == old(q.q1s.bst_root)
    ensures old(x.p) == null ==> Br'.bst == Br.bst 
    ensures old(x.p) != null ==> Br'.bst == Br.bst + {old(x.p)}
    ensures Br'.list == {}

method BSTDeleteInside(ghost Br: QueueBr, q: Queue, ghost root: QueueNode, x: QueueNode)
    returns (ghost Br': QueueBr, ret: QueueNode?, node: QueueNode)
    requires Br.bst == {} && Br.list == {}
    requires x.LC() && x.p != null
    requires x.p.l == x || x.p.r == x
    requires !(x.p.l == x && x.p.r == x)
    requires x.bst_root == root
    requires x.next == null && x.prev == null
    requires q.q1s != null ==> x != q.q1s
    modifies x.bst_root.bst_repr
    ensures ret == null || ret == old(x.l) || ret == old(x.r)
    ensures (old(x.bst_repr) == {x} ==> ret == null)
    ensures (old(x.bst_repr) > {x} ==> ret != null)
    ensures (ret != null ==> 
                ret.LC()
                && ret.bst_keys == old(x.bst_keys) - {x.k}
                && ret.min >= old(x.min)
                && ret.max <= old(x.max)
                && ret.bst_repr == old(x.bst_repr) - {x}
                && ret.bst_root == root
                && ret.p == old(x.p)
                && ret.List_FieldsUnchanged())
    ensures root.bst_keys == old(root.bst_keys) - {x.k}
    ensures root.min == old(root.min)
    ensures root.max == old(root.max)
    ensures root.bst_repr == old(root.bst_repr) - {x}
    ensures root.bst_root == old(root.bst_root)
    ensures root.p == old(root.p)
    ensures root.List_FieldsUnchanged()
    ensures node == x && node.k == old(x.k)
    ensures node.LC() && node.BST_Isolated()
    ensures node.List_FieldsUnchanged()
    ensures q.q1s != null ==> q.q1s.List_FieldsUnchanged() && q.q1s.bst_root == old(q.q1s.bst_root)
    ensures Br'.list == {} && Br'.bst == {}
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
    Br', ret, node := BSTRemoveRootInside(Br', q, x);
    ghost var cur := p;

    IfNotBrList_ThenList_LC(Br', cur);

    label PreLoop0:
    while cur.p != null
        invariant Br'.bst == {cur} && Br'.list == {}
        invariant cur.LC_Trans_PlusNode(node)
        invariant node.k in cur.bst_keys
        invariant cur.p != null && cur.l != null ==> (
            node !in cur.l.bst_repr 
            && node.k !in cur.l.bst_keys
            && cur.min <= cur.l.min
            && cur.l.max < cur.k
        )
        invariant cur.p != null && cur.r != null ==> (
            node !in cur.r.bst_repr 
            && node.k !in cur.r.bst_keys
            && cur.k < cur.r.min
            && cur.r.max <= cur.max
        )
        invariant cur.p == null && cur.r != null ==> (
            node !in cur.r.bst_repr
            && node.k !in cur.r.bst_keys
        )
        invariant cur in root.bst_repr
        invariant cur.bst_root == root
        invariant cur.p != null ==> cur.k != node.k
        invariant unchanged@PreLoop0(root)
        invariant unchanged@PreLoop0(node)
        invariant ret != null ==> unchanged@PreLoop0(ret)
        invariant q.q1s != null ==> q.q1s.List_FieldsUnchanged() && q.q1s.bst_root == old(q.q1s.bst_root)
        decreases cur.bst_depth
    {
        IfNotBr_ThenLC(Br', cur.p);
        if cur.l != null {
            IfNotBr_ThenLC(Br', cur.l);
        }
        if cur.r != null {
            IfNotBr_ThenLC(Br', cur.r);
        }
        Br' := cur.Set_bst_repr(Br', (if cur.l == null then {} else cur.l.bst_repr)
                                + {cur}
                                + (if cur.r == null then {} else cur.r.bst_repr));
        Br' := cur.Set_bst_keys(Br', (if cur.l == null then {} else cur.l.bst_keys)
                                + {cur.k}
                                + (if cur.r == null then {} else cur.r.bst_keys));
        Br' := cur.Set_min(Br', if cur.l == null then cur.k else cur.l.min);
        Br' := cur.Set_max(Br', if cur.r == null then cur.k else cur.r.max);
        Br' := AssertLCAndRemove(Br', cur);
        cur := cur.p;
        IfNotBrList_ThenList_LC(Br', cur);
    }

    Br' := cur.DeleteFromRootRepr(Br', node);
    Br' := cur.Set_bst_keys(Br', (if cur.r == null then {} else cur.r.bst_keys));
    Br' := AssertLCAndRemove(Br', cur);

    if ret != null {
        IfNotBr_ThenLC(Br', ret);
    }
}


