// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions"
// by Adithya Murali, Cody Rivera, and P. Madhusudan.
// 
// Artifact by Cody Rivera, 2023-2024. 
//
// Verification of Scheduler Queue Move Request.

include "scheduler-queue.dfy"

method {:extern} ListRemoveFirst(ghost Br: QueueBr, q: Queue, x: QueueNode?)
    returns (ghost Br': QueueBr, ret: QueueNode?, node: QueueNode?)
    requires Br.list == {} && Br.bst == {}
    requires x != null ==> x.LC() && x.prev == null
    modifies if x == null then {} else x.list_repr
    ensures x == null ==> ret == null
    ensures x != null ==> ret == old(x.next)
    ensures node == x
    ensures (ret != null ==>
                ret.LC()
                && ret.prev == null
                && ret.list_repr == old(x.list_repr) - {node}
                && ret.list_keys == old(x.list_keys) - {node.k}
                && ret.BST_FieldsUnchanged())
    ensures (node != null ==> 
                node.LC()
                && node.k == old(x.k)
                && node.next == null
                && node.prev == null
                && node.BST_FieldsUnchanged())
    ensures q.q1t != null ==> q.q1t.BST_FieldsUnchanged()
    ensures Br'.list == {} && Br'.bst == {}

method {:extern} BSTDeleteInside(ghost Br: QueueBr, q: Queue, ghost root: QueueNode, x: QueueNode)
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

/**
 * Deletes a request from q1s and q1t at the same time. 
 *
 * by Cody Rivera, 2023-2024
 */
method MoveRequest(ghost Br: QueueBr, q: Queue)
    returns (ghost Br': QueueBr, c: QueueNode?)
    requires Br.bst == {} && Br.list == {}
    requires q.Valid()
    modifies q, q.q1t.bst_repr
    ensures q.Valid() && Br'.bst == {} && Br'.list == {}
    ensures old(q.q1s) == null ==> 
                q.q1s == null
                && q.q1t.bst_keys == {}
                && q.q1t.bst_repr == {q.q1t}
    ensures old(q.q1s) != null ==>
                (old(q.q1s.list_keys) == {old(q.q1s.k)} ==> q.q1s == null)
                && (old(q.q1s.list_keys) > {old(q.q1s.k)} ==> q.q1s != null)
                && q.q1t.bst_keys == old(q.q1t.bst_keys) - {old(q.q1s.k)}
                && q.q1t.bst_repr == old(q.q1t.bst_repr) - {old(q.q1s)}
    ensures old(q.q1s) != null && q.q1s != null ==>
                && q.q1s.list_keys == old(q.q1s.list_keys) - {old(q.q1s.k)}
                && q.q1s.list_repr == old(q.q1s.list_repr) - {old(q.q1s)}
{
    Br' := Br;
    // First phase: remove the first element from the list.
    Br', q.q1s, c := ListRemoveFirst(Br, q, q.q1s);
    if c == null {
        return;
    }

    // Second phase: remove c from the BST q.q1t
    var tmp, c';
    if c.p != null {
        IfNotBr_ThenLC(Br', c.p);
    }
    Br', tmp, c' := BSTDeleteInside(Br', q, q.q1t, c);
    IfNotBr_ThenLC(Br', q.q1t);
    if q.q1t.l != null {
        IfNotBr_ThenLC(Br', q.q1t.l);
    }
    if q.q1t.r != null {
        IfNotBr_ThenLC(Br', q.q1t.r);
    }
    if q.q1s != null {
        IfNotBr_ThenLC(Br', q.q1s);
    }
}
