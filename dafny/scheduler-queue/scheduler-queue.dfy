// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions"
// by Anonymous Authors.
// 
// Artifact by Anonymous Author, 2023-2024. 
//
// Definition of the scheduler queue data structure
// (overlay of list and BST).

/**
 * Queue, with list pointers 
 */
class Queue {
    var q1s: QueueNode?
    var q1t: QueueNode?

    ghost predicate Valid()
        reads *
    {
        q1t != null // We always have the scaffold
        && q1t.p == null && q1t.LC()
        && (q1s == null <==> (q1t.l == null && q1t.r == null))
        && (q1s == null ==> 
                q1t.bst_repr == {q1t}
                && q1t.bst_keys == {})
        && (q1s != null ==> 
                q1s.LC()
                && q1s.prev == null
                && q1s.bst_root == q1t
                && q1s.list_repr == q1t.bst_repr - {q1t}
                && q1s.list_keys == q1t.bst_keys)
    }
}

/**
 * Broken set tuple
 */
datatype QueueBr = QueueBr(bst: set<QueueNode>, list: set<QueueNode>)

/**
    * Queue node with both BSTs and Lists
    */
class QueueNode {
    var k: int

    // bst
    var l: QueueNode?
    var r: QueueNode?
    var p: QueueNode?
    ghost var min: int
    ghost var max: int
    ghost var bst_keys: set<int>
    ghost var bst_repr: set<QueueNode>
    ghost var bst_depth: nat
    ghost var bst_root: QueueNode

    // list
    var next: QueueNode?
    ghost var prev: QueueNode?
    ghost var list_keys: set<int>
    ghost var list_repr: set<QueueNode>

    constructor (k: int) 
        ensures this.k == k 
        ensures this.l == null
        ensures this.r == null
        ensures this.p == this
        ensures this.next == null
        ensures this.prev == null
        ensures this.bst_root == this
    {
        this.k := k;
        this.l := null;
        this.r := null;
        this.p := this;
        this.next := null;
        this.prev := null;
        this.bst_root := this;
    }

    ghost predicate BST_LC()
        reads this, this.p, this.l, this.r, this.bst_repr, this.bst_root
    {
        (this == this.bst_root ==>
            this in this.bst_repr
            && this.p == null
            && this.bst_depth == 0
            && this.l == null
            && (this.r == null ==> 
                    this.bst_repr == {this}
                    && this.bst_keys == {})
            && (this.r != null ==>
                    this.r.p == this
                    && this.bst_repr == {this} + this.r.bst_repr
                    && this !in this.r.bst_repr
                    && this.bst_keys == this.r.bst_keys))
        && (this != this.bst_root ==>
                this in this.bst_repr
                && this.min <= this.k <= this.max
                && this.p != null
                && this.p !in this.bst_repr
                && (this.p.l == this || this.p.r == this)
                && this.bst_root !in this.bst_repr
                && this.bst_depth == this.p.bst_depth + 1
                && (this.l != null ==> 
                        this.l in this.bst_repr
                        && this !in this.l.bst_repr
                        && this.l.p == this
                        && this.l.max < this.k)
                && (this.r != null ==> 
                        this.r in this.bst_repr
                        && this !in this.r.bst_repr
                        && this.r.p == this
                        && this.r.min > this.k)
                && (this.l == null && this.r == null ==>
                        this.bst_repr == {this}
                        && this.bst_keys == {this.k}
                        && this.min == this.k == this.max
                        )
                && (this.l != null && this.r == null ==>
                        this.bst_repr == this.l.bst_repr + {this}
                        && this.bst_keys == this.l.bst_keys + {this.k}
                        && this.k !in this.l.bst_keys
                        && this.min == this.l.min && this.max == this.k
                        )
                && (this.l == null && this.r != null ==>
                        this.bst_repr == {this} + this.r.bst_repr
                        && this.bst_keys == {this.k} + this.r.bst_keys
                        && this.k !in this.r.bst_keys
                        && this.min == this.k && this.max == this.r.max
                        )
                && (this.l != null && this.r != null ==>
                        this.bst_repr == this.l.bst_repr + {this} + this.r.bst_repr
                        && this.l.bst_repr !! this.r.bst_repr
                        && this.bst_keys == this.l.bst_keys + {this.k} + this.r.bst_keys
                        && this.l.bst_keys !! this.r.bst_keys
                        && this.k !in this.l.bst_keys && this.k !in this.r.bst_keys
                        && this.min == this.l.min && this.max == this.r.max
                        )
                // Special scaffold properties.
                && this.bst_root == this.p.bst_root
                && this in this.bst_root.bst_repr
                && this.p in this.bst_root.bst_repr
                && (this.l != null ==> this.l in this.bst_root.bst_repr)
                && (this.r != null ==> this.r in this.bst_root.bst_repr)
                && this.bst_root.p == null
        )
    }

    ghost predicate List_LC()
        reads this, this.next, this.prev, this.list_repr
    {
        this in this.list_repr
        && (this.prev != null ==>
                this.prev !in this.list_repr
                && this.prev.next == this)
        && (this.next == null ==>
                this.list_repr == {this}
                && this.list_keys == {this.k})
        && (this.next != null ==>
                this.next in this.list_repr
                && this.list_repr == this.next.list_repr + {this}
                && this !in this.next.list_repr
                && this.list_keys == this.next.list_keys + {this.k}
                && this.k !in this.next.list_keys
                && this.next.prev == this
                && this.bst_root == this.next.bst_root)
    }

    ghost predicate LC()
        reads this, this.p, this.l, this.r, this.bst_repr, this.bst_root,
                this.next, this.prev, this.list_repr
    {
        BST_LC()
        && List_LC()
    }

    ghost predicate BST_LC_Trans_NoDepth()
        reads this, this.p, this.l, this.r, this.bst_repr, this.bst_root
    {
        (this == this.bst_root ==>
            this in this.bst_repr
            && this.p == null
            //&& this.bst_depth == 0
            && this.l == null
            && (this.r == null ==> 
                    this.bst_repr == {this}
                    && this.bst_keys == {})
            && (this.r != null ==>
                    this.r.p == this
                    && this.bst_repr == {this} + this.r.bst_repr
                    && this !in this.r.bst_repr
                    && this.bst_keys == this.r.bst_keys))
        && (this != this.bst_root ==>
                this in this.bst_repr
                && this.min <= this.k <= this.max
                && this.p != null
                && this.p !in this.bst_repr
                && (this.p.l == this || this.p.r == this)
                && this.bst_root !in this.bst_repr
                //&& this.bst_depth == this.p.bst_depth + 1
                && (this.l != null ==> 
                        this.l in this.bst_repr
                        && this !in this.l.bst_repr
                        && this.l.p == this
                        && this.l.max < this.k)
                && (this.r != null ==> 
                        this.r in this.bst_repr
                        && this !in this.r.bst_repr
                        && this.r.p == this
                        && this.r.min > this.k)
                && (this.l == null && this.r == null ==>
                        this.bst_repr == {this}
                        && this.bst_keys == {this.k}
                        && this.min == this.k == this.max
                        )
                && (this.l != null && this.r == null ==>
                        this.bst_repr == this.l.bst_repr + {this}
                        && this.bst_keys == this.l.bst_keys + {this.k}
                        && this.k !in this.l.bst_keys
                        && this.min == this.l.min && this.max == this.k
                        )
                && (this.l == null && this.r != null ==>
                        this.bst_repr == {this} + this.r.bst_repr
                        && this.bst_keys == {this.k} + this.r.bst_keys
                        && this.k !in this.r.bst_keys
                        && this.min == this.k && this.max == this.r.max
                        )
                && (this.l != null && this.r != null ==>
                        this.bst_repr == this.l.bst_repr + {this} + this.r.bst_repr
                        && this.l.bst_repr !! this.r.bst_repr
                        && this.bst_keys == this.l.bst_keys + {this.k} + this.r.bst_keys
                        && this.l.bst_keys !! this.r.bst_keys
                        && this.k !in this.l.bst_keys && this.k !in this.r.bst_keys
                        && this.min == this.l.min && this.max == this.r.max
                        )
                // Special scaffold properties.
                && this.bst_root == this.p.bst_root
                && this in this.bst_root.bst_repr
                && this.p in this.bst_root.bst_repr
                && (this.l != null ==> this.l in this.bst_root.bst_repr)
                && (this.r != null ==> this.r in this.bst_root.bst_repr)
                && this.bst_root.p == null
        )
    }

    ghost predicate LC_Trans_NoDepth()
        reads this, this.p, this.l, this.r, this.bst_repr, this.bst_root,
                this.next, this.prev, this.list_repr
    {
        BST_LC_Trans_NoDepth()
        && List_LC()
    }

    ghost predicate BST_LC_Trans_PlusNode(node: QueueNode)
        reads this, this.p, this.l, this.r, this.bst_repr, this.bst_root
    {
        (this == this.bst_root ==>
            this in this.bst_repr
            && this.p == null
            && this.bst_depth == 0
            && this.l == null
            && (this.r == null ==> 
                    this.bst_repr == {this, node}
                    && this.bst_keys == {node.k})
            && (this.r != null ==>
                    this.r.p == this
                    && this.bst_repr == {this} + this.r.bst_repr + {node}
                    && this !in this.r.bst_repr
                    && this.bst_keys == this.r.bst_keys + {node.k}))
        && (this != this.bst_root ==>
                this in this.bst_repr
                && this.min <= this.k <= this.max
                && this.p != null
                && this.p !in this.bst_repr
                && (this.p.l == this || this.p.r == this)
                && this.bst_root !in this.bst_repr
                && this.bst_depth == this.p.bst_depth + 1
                && (this.l != null ==> 
                        this.l in this.bst_repr
                        && this !in this.l.bst_repr
                        && this.l.p == this
                        && this.l.max < this.k
                        )
                && (this.r != null ==> 
                        this.r in this.bst_repr
                        && this !in this.r.bst_repr
                        && this.r.p == this
                        && this.r.min > this.k
                        )
                && (this.l == null && this.r == null ==>
                        this.bst_repr == {this, node}
                        && this.bst_keys == {this.k, node.k}
                        //&& this.min == this.k == this.max
                        )
                && (this.l != null && this.r == null ==>
                        this.bst_repr == this.l.bst_repr + {this} + {node}
                        && this.bst_keys == this.l.bst_keys + {this.k} + {node.k}
                        && this.k !in this.l.bst_keys
                        //&& this.min == this.l.min && this.max == this.k
                        )
                && (this.l == null && this.r != null ==>
                        this.bst_repr == {this} + this.r.bst_repr + {node}
                        && this.bst_keys == {this.k} + this.r.bst_keys + {node.k}
                        && this.k !in this.r.bst_keys
                        //&& this.min == this.k && this.max == this.r.max
                        )
                && (this.l != null && this.r != null ==>
                        this.bst_repr == this.l.bst_repr + {this} + this.r.bst_repr + {node}
                        && this.l.bst_repr !! this.r.bst_repr
                        && this.bst_keys == this.l.bst_keys + {this.k} + this.r.bst_keys + {node.k}
                        && this.l.bst_keys !! this.r.bst_keys
                        && this.k !in this.l.bst_keys && this.k !in this.r.bst_keys
                        //&& this.min == this.l.min && this.max == this.r.max
                        )
                // Special scaffold properties.
                && this.bst_root == this.p.bst_root
                && this in this.bst_root.bst_repr
                && this.p in this.bst_root.bst_repr
                && (this.l != null ==> this.l in this.bst_root.bst_repr)
                && (this.r != null ==> this.r in this.bst_root.bst_repr)
                && this.bst_root.p == null
        )
    }

    ghost predicate LC_Trans_PlusNode(node: QueueNode)
        reads this, this.p, this.l, this.r, this.bst_repr, this.bst_root,
                this.next, this.prev, this.list_repr
    {
        BST_LC_Trans_PlusNode(node)
        && List_LC()
    }

    ghost predicate BST_Isolated()
        reads this
    {
        this.p == null && this.l == null && this.r == null
    }

    twostate predicate BST_FieldsUnchanged()
        reads this
    {
        this.l == old(this.l)
        && this.r == old(this.r)
        && this.p == old(this.p)
        && this.min == old(this.min)
        && this.max == old(this.max)
        && this.bst_keys == old(this.bst_keys)
        && this.bst_repr == old(this.bst_repr)
        && this.bst_depth == old(this.bst_depth)
        && this.bst_root == old(this.bst_root)
    }

    twostate predicate List_FieldsUnchanged()
        reads this
    {
        this.next == old(this.next)
        && this.prev == old(this.prev)
        && this.list_keys == old(this.list_keys)
        && this.list_repr == old(this.list_repr)
    }

    twostate predicate FieldsUnchangedMinus_bst_depth()
        reads this
    {
        this.k == old(this.k)
        && this.l == old(this.l)
        && this.r == old(this.r)
        && this.p == old(this.p)
        && this.min == old(this.min)
        && this.max == old(this.max)
        && this.bst_keys == old(this.bst_keys)
        && this.bst_repr == old(this.bst_repr)
        && this.bst_root == old(this.bst_root)
        && this.next == old(this.next)
        && this.prev == old(this.prev)
        && this.list_keys == old(this.list_keys)
        && this.list_repr == old(this.list_repr)
    }

    /**
        * Data structure manipulation macros.
        * We must prove that these macros update
        * Br correctly.
        */
    static method Create(ghost Br: QueueBr, k: int)
        returns (ghost Br': QueueBr, node: QueueNode)
        ensures node.k == k
        ensures node.l == null
        ensures node.r == null
        ensures node.p == node
        ensures node.next == null
        ensures node.prev == null
        ensures node.bst_root == node
        ensures fresh(node)
        ensures Br' == QueueBr(Br.list + {node}, Br.bst + {node})
    {
        node := new QueueNode(k);
        Br' := QueueBr(Br.list + {node}, Br.bst + {node});
    }

    method Set_k(ghost Br: QueueBr, k: int)
        returns (ghost Br': QueueBr)
        modifies this
        ensures this.k == k
        ensures this.l == old(this.l)
        ensures this.r == old(this.r)
        ensures this.p == old(this.p)
        ensures this.min == old(this.min)
        ensures this.max == old(this.max)
        ensures this.bst_keys == old(this.bst_keys)
        ensures this.bst_repr == old(this.bst_repr)
        ensures this.bst_depth == old(this.bst_depth)
        ensures this.bst_root == old(this.bst_root)
        ensures this.next == old(this.next)
        ensures this.prev == old(this.prev)
        ensures this.list_keys == old(this.list_keys)
        ensures this.list_repr == old(this.list_repr)
        ensures Br' == QueueBr(Br.bst + {this}, Br.list + {this})
    {
        Br' := Br;
        this.k := k;
        Br' := QueueBr(Br'.bst + {this}, Br'.list + {this});
    }

    method Set_l(ghost Br: QueueBr, l: QueueNode?)
        returns (ghost Br': QueueBr)
        modifies this
        ensures this.k == old(this.k)
        ensures this.l == l
        ensures this.r == old(this.r)
        ensures this.p == old(this.p)
        ensures this.min == old(this.min)
        ensures this.max == old(this.max)
        ensures this.bst_keys == old(this.bst_keys)
        ensures this.bst_repr == old(this.bst_repr)
        ensures this.bst_depth == old(this.bst_depth)
        ensures this.bst_root == old(this.bst_root)
        ensures this.next == old(this.next)
        ensures this.prev == old(this.prev)
        ensures this.list_keys == old(this.list_keys)
        ensures this.list_repr == old(this.list_repr)
        ensures old(this.l) == null ==> Br'.bst == Br.bst + {this}
        ensures old(this.l) != null ==> Br'.bst == Br.bst + {this, old(this.l)}
        ensures Br'.list == Br.list
    {
        Br' := Br;
        if this.l != null {
            Br' := Br'.(bst := Br'.bst + {this.l});
        }
        this.l := l;
        Br' := Br'.(bst := Br'.bst + {this});
    }

    method Set_r(ghost Br: QueueBr, r: QueueNode?)
        returns (ghost Br': QueueBr)
        modifies this
        ensures this.k == old(this.k)
        ensures this.l == old(this.l)
        ensures this.r == r
        ensures this.p == old(this.p)
        ensures this.min == old(this.min)
        ensures this.max == old(this.max)
        ensures this.bst_keys == old(this.bst_keys)
        ensures this.bst_repr == old(this.bst_repr)
        ensures this.bst_depth == old(this.bst_depth)
        ensures this.bst_root == old(this.bst_root)
        ensures this.next == old(this.next)
        ensures this.prev == old(this.prev)
        ensures this.list_keys == old(this.list_keys)
        ensures this.list_repr == old(this.list_repr)
        ensures old(this.r) == null ==> Br'.bst == Br.bst + {this}
        ensures old(this.r) != null ==> Br'.bst == Br.bst + {this, old(this.r)}
        ensures Br'.list == Br.list
    {
        Br' := Br;
        if this.r != null {
            Br' := Br'.(bst := Br'.bst + {this.r});
        }
        this.r := r;
        Br' := Br'.(bst := Br'.bst + {this});
    }

    method Set_p(ghost Br: QueueBr, p: QueueNode?)
        returns (ghost Br': QueueBr)
        requires this.p != null
        modifies this
        ensures this.k == old(this.k)
        ensures this.l == old(this.l)
        ensures this.r == old(this.r)
        ensures this.p == p
        ensures this.min == old(this.min)
        ensures this.max == old(this.max)
        ensures this.bst_keys == old(this.bst_keys)
        ensures this.bst_repr == old(this.bst_repr)
        ensures this.bst_depth == old(this.bst_depth)
        ensures this.bst_root == old(this.bst_root)
        ensures this.next == old(this.next)
        ensures this.prev == old(this.prev)
        ensures this.list_keys == old(this.list_keys)
        ensures this.list_repr == old(this.list_repr)
        ensures old(this.p) == null ==> Br'.bst == Br.bst + {this}
        ensures old(this.p) != null ==> Br'.bst == Br.bst + {this, old(this.p)}
        ensures Br'.list == Br.list
    {
        Br' := Br;
        if this.p != null {
            Br' := Br'.(bst := Br'.bst + {this.p});
        }
        this.p := p;
        Br' := Br'.(bst := Br'.bst + {this});
    }

    ghost method Set_min(Br: QueueBr, min: int)
        returns (Br': QueueBr)
        modifies this
        ensures this.k == old(this.k)
        ensures this.l == old(this.l)
        ensures this.r == old(this.r)
        ensures this.p == old(this.p)
        ensures this.min == min
        ensures this.max == old(this.max)
        ensures this.bst_keys == old(this.bst_keys)
        ensures this.bst_repr == old(this.bst_repr)
        ensures this.bst_depth == old(this.bst_depth)
        ensures this.bst_root == old(this.bst_root)
        ensures this.next == old(this.next)
        ensures this.prev == old(this.prev)
        ensures this.list_keys == old(this.list_keys)
        ensures this.list_repr == old(this.list_repr)
        ensures this.p == null ==> Br'.bst == Br.bst + {this}
        ensures this.p != null ==> Br'.bst == Br.bst + {this, this.p}
        ensures Br'.list == Br.list
    {
        Br' := Br;
        this.min := min;
        Br' := Br'.(bst := Br'.bst + {this});
        if this.p != null {
            Br' := Br'.(bst := Br'.bst + {this.p});
        }
    }

    ghost method Set_max(Br: QueueBr, max: int)
        returns (Br': QueueBr)
        modifies this
        ensures this.k == old(this.k)
        ensures this.l == old(this.l)
        ensures this.r == old(this.r)
        ensures this.p == old(this.p)
        ensures this.min == old(this.min)
        ensures this.max == max
        ensures this.bst_keys == old(this.bst_keys)
        ensures this.bst_repr == old(this.bst_repr)
        ensures this.bst_depth == old(this.bst_depth)
        ensures this.bst_root == old(this.bst_root)
        ensures this.next == old(this.next)
        ensures this.prev == old(this.prev)
        ensures this.list_keys == old(this.list_keys)
        ensures this.list_repr == old(this.list_repr)
        ensures this.p == null ==> Br'.bst == Br.bst + {this}
        ensures this.p != null ==> Br'.bst == Br.bst + {this, this.p}
        ensures Br'.list == Br.list
    {
        Br' := Br;
        this.max := max;
        Br' := Br'.(bst := Br'.bst + {this});
        if this.p != null {
            Br' := Br'.(bst := Br'.bst + {this.p});
        }
    }

    ghost method Set_bst_keys(Br: QueueBr, keys: set<int>)
        returns (Br': QueueBr)
        modifies this
        ensures this.k == old(this.k)
        ensures this.l == old(this.l)
        ensures this.r == old(this.r)
        ensures this.p == old(this.p)
        ensures this.min == old(this.min)
        ensures this.max == old(this.max)
        ensures this.bst_keys == keys
        ensures this.bst_repr == old(this.bst_repr)
        ensures this.bst_depth == old(this.bst_depth)
        ensures this.bst_root == old(this.bst_root)
        ensures this.next == old(this.next)
        ensures this.prev == old(this.prev)
        ensures this.list_keys == old(this.list_keys)
        ensures this.list_repr == old(this.list_repr)
        ensures this.p == null ==> Br'.bst == Br.bst + {this}
        ensures this.p != null ==> Br'.bst == Br.bst + {this, this.p}
        ensures Br'.list == Br.list
    {
        Br' := Br;
        this.bst_keys := keys;
        Br' := Br'.(bst := Br'.bst + {this});
        if this.p != null {
            Br' := Br'.(bst := Br'.bst + {this.p});
        }
    }

    ghost method Set_bst_repr(Br: QueueBr, repr: set<QueueNode>)
        returns (Br': QueueBr)
        requires this.p != null
        modifies this
        ensures this.k == old(this.k)
        ensures this.l == old(this.l)
        ensures this.r == old(this.r)
        ensures this.p == old(this.p)
        ensures this.min == old(this.min)
        ensures this.max == old(this.max)
        ensures this.bst_keys == old(this.bst_keys)
        ensures this.bst_repr == repr
        ensures this.bst_depth == old(this.bst_depth)
        ensures this.bst_root == old(this.bst_root)
        ensures this.next == old(this.next)
        ensures this.prev == old(this.prev)
        ensures this.list_keys == old(this.list_keys)
        ensures this.list_repr == old(this.list_repr)
        ensures this.p == null ==> Br'.bst == Br.bst + {this}
        ensures this.p != null ==> Br'.bst == Br.bst + {this, this.p}
        ensures Br'.list == Br.list
    {
        Br' := Br;
        this.bst_repr := repr;
        Br' := Br'.(bst := Br'.bst + {this});
        if this.p != null {
            Br' := Br'.(bst := Br'.bst + {this.p});
        }
    }

    ghost method Set_bst_depth(Br: QueueBr, depth: nat)
        returns (Br': QueueBr)
        modifies this
        ensures this.k == old(this.k)
        ensures this.l == old(this.l)
        ensures this.r == old(this.r)
        ensures this.p == old(this.p)
        ensures this.min == old(this.min)
        ensures this.max == old(this.max)
        ensures this.bst_keys == old(this.bst_keys)
        ensures this.bst_repr == old(this.bst_repr)
        ensures this.bst_root == old(this.bst_root)
        ensures this.bst_depth == depth
        ensures this.next == old(this.next)
        ensures this.prev == old(this.prev)
        ensures this.list_keys == old(this.list_keys)
        ensures this.list_repr == old(this.list_repr)
        ensures Br'.bst == Br.bst + {this}
                        + (if this.l == null then {} else {this.l})
                        + (if this.r == null then {} else {this.r})
        ensures Br'.list == Br.list
    {
        Br' := Br;
        this.bst_depth := depth;
        Br' := Br'.(bst := Br'.bst + {this});
        if this.l != null {
            Br' := Br'.(bst := Br'.bst + {this.l});
        }
        if this.r != null {
            Br' := Br'.(bst := Br'.bst + {this.r});
        }
    }

    ghost method Set_bst_root(Br: QueueBr, root: QueueNode)
        returns (Br': QueueBr)
        modifies this
        ensures this.k == old(this.k)
        ensures this.l == old(this.l)
        ensures this.r == old(this.r)
        ensures this.p == old(this.p)
        ensures this.min == old(this.min)
        ensures this.max == old(this.max)
        ensures this.bst_keys == old(this.bst_keys)
        ensures this.bst_repr == old(this.bst_repr)
        ensures this.bst_depth == old(this.bst_depth)
        ensures this.bst_root == root
        ensures this.next == old(this.next)
        ensures this.prev == old(this.prev)
        ensures this.list_keys == old(this.list_keys)
        ensures this.list_repr == old(this.list_repr)
        ensures Br'.bst == Br.bst + {this}
                        + (if this.l == null then {} else {this.l})
                        + (if this.r == null then {} else {this.r})
        ensures Br'.list == Br.list + {this}
                        + (if this.prev == null then {} else {this.prev})
    {
        Br' := Br;
        this.bst_root := root;
        Br' := Br'.(bst := Br'.bst + {this});
        Br' := Br'.(list := Br'.list + {this});
        if this.l != null {
            Br' := Br'.(bst := Br'.bst + {this.l});
        }
        if this.r != null {
            Br' := Br'.(bst := Br'.bst + {this.r});
        }
        if this.prev != null {
            Br' := Br'.(list := Br'.list + {this.prev});
        }
    }

    ghost method DeleteFromRootRepr(Br: QueueBr, node: QueueNode)
        returns (Br': QueueBr)
        requires this.p == null
        requires node.BST_Isolated()
        modifies this
        ensures this.k == old(this.k)
        ensures this.l == old(this.l)
        ensures this.r == old(this.r)
        ensures this.p == old(this.p)
        ensures this.min == old(this.min)
        ensures this.max == old(this.max)
        ensures this.bst_keys == old(this.bst_keys)
        ensures this.bst_repr == old(this.bst_repr) - {node}
        ensures this.bst_depth == old(this.bst_depth)
        ensures this.bst_root == old(this.bst_root)
        ensures this.next == old(this.next)
        ensures this.prev == old(this.prev)
        ensures this.list_keys == old(this.list_keys)
        ensures this.list_repr == old(this.list_repr)
        ensures Br'.bst == Br.bst + {this}
        ensures Br'.list == Br.list
    {
        Br' := Br;
        this.bst_repr := this.bst_repr - {node};
        Br' := Br'.(bst := Br'.bst + {this});
    }

    method Set_next(ghost Br: QueueBr, n: QueueNode?)
        returns (ghost Br': QueueBr)
        modifies this
        ensures this.k == old(this.k)
        ensures this.l == old(this.l)
        ensures this.r == old(this.r)
        ensures this.p == old(this.p)
        ensures this.min == old(this.min)
        ensures this.max == old(this.max)
        ensures this.bst_keys == old(this.bst_keys)
        ensures this.bst_repr == old(this.bst_repr)
        ensures this.bst_depth == old(this.bst_depth)
        ensures this.bst_root == old(this.bst_root)
        ensures this.next == n
        ensures this.prev == old(this.prev)
        ensures this.list_keys == old(this.list_keys)
        ensures this.list_repr == old(this.list_repr)
        ensures old(this.next) == null ==> Br'.list == Br.list + {this}
        ensures old(this.next) != null ==> Br'.list == Br.list + {this, old(this.next)}
        ensures Br'.bst == Br.bst
    {
        Br' := Br;
        if this.next != null {
            Br' := Br'.(list := Br'.list + {this.next});
        }
        this.next := n;
        Br' := Br'.(list := Br'.list + {this});
    }

    ghost method Set_prev(Br: QueueBr, p: QueueNode?)
        returns (Br': QueueBr)
        modifies this
        ensures this.k == old(this.k)
        ensures this.l == old(this.l)
        ensures this.r == old(this.r)
        ensures this.p == old(this.p)
        ensures this.min == old(this.min)
        ensures this.max == old(this.max)
        ensures this.bst_keys == old(this.bst_keys)
        ensures this.bst_repr == old(this.bst_repr)
        ensures this.bst_depth == old(this.bst_depth)
        ensures this.bst_root == old(this.bst_root)
        ensures this.next == old(this.next)
        ensures this.prev == p
        ensures this.list_keys == old(this.list_keys)
        ensures this.list_repr == old(this.list_repr)
        ensures old(this.prev) == null ==> Br'.list == Br.list + {this}
        ensures old(this.prev) != null ==> Br'.list == Br.list + {this, old(this.prev)}
        ensures Br'.bst == Br.bst
    {
        Br' := Br;
        if this.prev != null {
            Br' := Br'.(list := Br'.list + {this.prev});
        }
        this.prev := p;
        Br' := Br'.(list := Br'.list + {this});
    }

    ghost method Set_list_keys(Br: QueueBr, keys: set<int>)
        returns (Br': QueueBr)
        modifies this
        ensures this.k == old(this.k)
        ensures this.l == old(this.l)
        ensures this.r == old(this.r)
        ensures this.p == old(this.p)
        ensures this.min == old(this.min)
        ensures this.max == old(this.max)
        ensures this.bst_keys == old(this.bst_keys)
        ensures this.bst_repr == old(this.bst_repr)
        ensures this.bst_depth == old(this.bst_depth)
        ensures this.bst_root == old(this.bst_root)
        ensures this.next == old(this.next)
        ensures this.prev == old(this.prev)
        ensures this.list_keys == keys
        ensures this.list_repr == old(this.list_repr)
        ensures this.prev == null ==> Br'.list == Br.list + {this}
        ensures this.prev != null ==> Br'.list == Br.list + {this, this.prev}
        ensures Br'.bst == Br.bst
    {
        Br' := Br;
        this.list_keys := keys;
        Br' := Br'.(list := Br'.list + {this});
        if this.prev != null {
            Br' := Br'.(list := Br'.list + {this.prev});
        }
    }

    ghost method Set_list_repr(Br: QueueBr, repr: set<QueueNode>)
        returns (Br': QueueBr)
        modifies this
        ensures this.k == old(this.k)
        ensures this.l == old(this.l)
        ensures this.r == old(this.r)
        ensures this.p == old(this.p)
        ensures this.min == old(this.min)
        ensures this.max == old(this.max)
        ensures this.bst_keys == old(this.bst_keys)
        ensures this.bst_repr == old(this.bst_repr)
        ensures this.bst_depth == old(this.bst_depth)
        ensures this.bst_root == old(this.bst_root)
        ensures this.next == old(this.next)
        ensures this.prev == old(this.prev)
        ensures this.list_keys == old(this.list_keys)
        ensures this.list_repr == repr
        ensures this.prev == null ==> Br'.list == Br.list + {this}
        ensures this.prev != null ==> Br'.list == Br.list + {this, this.prev}
        ensures Br'.bst == Br.bst
    {
        Br' := Br;
        this.list_repr := repr;
        Br' := Br'.(list := Br'.list + {this});
        if this.prev != null {
            Br' := Br'.(list := Br'.list + {this.prev});
        }
    }
}

lemma {:axiom} IfNotBr_ThenLC(Br: QueueBr, x: QueueNode?)
    ensures x != null && x !in Br.bst && x !in Br.list ==> x.LC()

lemma {:axiom} IfNotBrList_ThenList_LC(Br: QueueBr, x: QueueNode?)
    ensures x != null && x !in Br.list ==> x.List_LC()

ghost method AssertLCAndRemove(Br: QueueBr, x: QueueNode?)
    returns (Br': QueueBr)
    ensures (x != null && x.LC()) ==> Br' == QueueBr(Br.bst - {x}, Br.list - {x})
    ensures (x == null || !x.LC()) ==> Br' == Br
{
    if x != null && x.LC() {
        Br' := QueueBr(Br.bst - {x}, Br.list - {x});
    } else {
        Br' := Br;
    }
}
