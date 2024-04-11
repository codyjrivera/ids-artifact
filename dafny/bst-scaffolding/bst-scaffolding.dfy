// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions"
// by Adithya Murali, Cody Rivera, and P. Madhusudan.
// 
// Artifact by Cody Rivera, 2023-2024. 
//
// Definition of binary search trees with scaffolding.

class BSTNode {
    var k: int
    var l: BSTNode?
    var r: BSTNode?
    var p: BSTNode?
    ghost var min: int
    ghost var max: int
    ghost var keys: set<int>
    ghost var repr: set<BSTNode>
    ghost var root: BSTNode
    ghost var depth: nat

    constructor (k: int) 
        ensures this.k == k 
        ensures this.l == null
        ensures this.r == null
        ensures this.p == null
        ensures this.root == this
    {
        this.k := k;
        this.l := null;
        this.r := null;
        this.p := null;
        this.root := this;
    }

    ghost predicate LC()
        reads *
    {
        (this == this.root ==>
            this in this.repr
            && this.p == null
            && this.depth == 0
            && this.l == null
            && (this.r == null ==> 
                    this.repr == {this}
                    && this.keys == {})
            && (this.r != null ==>
                    this.r.p == this
                    && this.repr == {this} + this.r.repr
                    && this !in this.r.repr
                    && this.keys == this.r.keys))
        && (this != this.root ==>
                this in this.repr
                && this.min <= this.k <= this.max
                && this.p != null
                && this.p !in this.repr
                && (this.p.l == this || this.p.r == this)
                && this.root !in this.repr
                && this.depth == this.p.depth + 1
                && (this.l != null ==> 
                        this.l in this.repr
                        && this !in this.l.repr
                        && this.l.p == this
                        && this.l.max < this.k)
                && (this.r != null ==> 
                        this.r in this.repr
                        && this !in this.r.repr
                        && this.r.p == this
                        && this.r.min > this.k)
                && (this.l == null && this.r == null ==>
                        this.repr == {this}
                        && this.keys == {this.k}
                        && this.min == this.k == this.max
                        )
                && (this.l != null && this.r == null ==>
                        this.repr == this.l.repr + {this}
                        && this.keys == this.l.keys + {this.k}
                        && this.k !in this.l.keys
                        && this.min == this.l.min && this.max == this.k
                        )
                && (this.l == null && this.r != null ==>
                        this.repr == {this} + this.r.repr
                        && this.keys == {this.k} + this.r.keys
                        && this.k !in this.r.keys
                        && this.min == this.k && this.max == this.r.max
                        )
                && (this.l != null && this.r != null ==>
                        this.repr == this.l.repr + {this} + this.r.repr
                        && this.l.repr !! this.r.repr
                        && this.keys == this.l.keys + {this.k} + this.r.keys
                        && this.l.keys !! this.r.keys
                        && this.k !in this.l.keys && this.k !in this.r.keys
                        && this.min == this.l.min && this.max == this.r.max
                        )
                // Special scaffold properties.
                && this.root == this.p.root
                && this in this.root.repr
                && this.p in this.root.repr
                && (this.l != null ==> this.l in this.root.repr)
                && (this.r != null ==> this.r in this.root.repr)
                && this.root.p == null
        )
    }

    ghost predicate LC_Trans_NoDepth()
        reads *
    {
        (this == this.root ==>
            this in this.repr
            && this.p == null
            //&& this.depth == 0
            && this.l == null
            && (this.r == null ==> 
                    this.repr == {this}
                    && this.keys == {})
            && (this.r != null ==>
                    this.r.p == this
                    && this.repr == {this} + this.r.repr
                    && this !in this.r.repr
                    && this.keys == this.r.keys))
        && (this != this.root ==>
                this in this.repr
                && this.min <= this.k <= this.max
                && this.p != null
                && this.p !in this.repr
                && (this.p.l == this || this.p.r == this)
                && this.root !in this.repr
                //&& this.depth == this.p.depth + 1
                && (this.l != null ==> 
                        this.l in this.repr
                        && this !in this.l.repr
                        && this.l.p == this
                        && this.l.max < this.k)
                && (this.r != null ==> 
                        this.r in this.repr
                        && this !in this.r.repr
                        && this.r.p == this
                        && this.r.min > this.k)
                && (this.l == null && this.r == null ==>
                        this.repr == {this}
                        && this.keys == {this.k}
                        && this.min == this.k == this.max
                        )
                && (this.l != null && this.r == null ==>
                        this.repr == this.l.repr + {this}
                        && this.keys == this.l.keys + {this.k}
                        && this.k !in this.l.keys
                        && this.min == this.l.min && this.max == this.k
                        )
                && (this.l == null && this.r != null ==>
                        this.repr == {this} + this.r.repr
                        && this.keys == {this.k} + this.r.keys
                        && this.k !in this.r.keys
                        && this.min == this.k && this.max == this.r.max
                        )
                && (this.l != null && this.r != null ==>
                        this.repr == this.l.repr + {this} + this.r.repr
                        && this.l.repr !! this.r.repr
                        && this.keys == this.l.keys + {this.k} + this.r.keys
                        && this.l.keys !! this.r.keys
                        && this.k !in this.l.keys && this.k !in this.r.keys
                        && this.min == this.l.min && this.max == this.r.max
                        )
                // Special scaffold properties.
                && this.root == this.p.root
                && this in this.root.repr
                && this.p in this.root.repr
                && (this.l != null ==> this.l in this.root.repr)
                && (this.r != null ==> this.r in this.root.repr)
                && this.root.p == null
        )
    }

    ghost predicate LC_Trans_PlusNode(node: BSTNode)
        reads *
    {
        (this == this.root ==>
            this in this.repr
            && this.p == null
            && this.depth == 0
            && this.l == null
            && (this.r == null ==> 
                    this.repr == {this, node}
                    && this.keys == {node.k})
            && (this.r != null ==>
                    this.r.p == this
                    && this.repr == {this} + this.r.repr + {node}
                    && this !in this.r.repr
                    && this.keys == this.r.keys + {node.k}))
        && (this != this.root ==>
                this in this.repr
                && this.min <= this.k <= this.max
                && this.p != null
                && this.p !in this.repr
                && (this.p.l == this || this.p.r == this)
                && this.root !in this.repr
                && this.depth == this.p.depth + 1
                && (this.l != null ==> 
                        this.l in this.repr
                        && this !in this.l.repr
                        && this.l.p == this
                        && this.l.max < this.k
                        )
                && (this.r != null ==> 
                        this.r in this.repr
                        && this !in this.r.repr
                        && this.r.p == this
                        && this.r.min > this.k
                        )
                && (this.l == null && this.r == null ==>
                        this.repr == {this, node}
                        && this.keys == {this.k, node.k}
                        //&& this.min == this.k == this.max
                        )
                && (this.l != null && this.r == null ==>
                        this.repr == this.l.repr + {this} + {node}
                        && this.keys == this.l.keys + {this.k} + {node.k}
                        && this.k !in this.l.keys
                        //&& this.min == this.l.min && this.max == this.k
                        )
                && (this.l == null && this.r != null ==>
                        this.repr == {this} + this.r.repr + {node}
                        && this.keys == {this.k} + this.r.keys + {node.k}
                        && this.k !in this.r.keys
                        //&& this.min == this.k && this.max == this.r.max
                        )
                && (this.l != null && this.r != null ==>
                        this.repr == this.l.repr + {this} + this.r.repr + {node}
                        && this.l.repr !! this.r.repr
                        && this.keys == this.l.keys + {this.k} + this.r.keys + {node.k}
                        && this.l.keys !! this.r.keys
                        && this.k !in this.l.keys && this.k !in this.r.keys
                        //&& this.min == this.l.min && this.max == this.r.max
                        )
                // Special scaffold properties.
                && this.root == this.p.root
                && this in this.root.repr
                && this.p in this.root.repr
                && (this.l != null ==> this.l in this.root.repr)
                && (this.r != null ==> this.r in this.root.repr)
                && this.root.p == null
        )
    }

    ghost predicate Isolated()
        reads this
    {
        this.l == null && this.r == null && this.p == null
    }

    /**
        * Data structure manipulation macros.
        * We must prove that these macros update
        * Br correctly.
        */
    static method Create(ghost Br: set<BSTNode>, k: int)
        returns (ghost Br': set<BSTNode>, node: BSTNode)
        ensures node.k == k
        ensures node.l == null
        ensures node.r == null
        ensures node.p == null
        ensures node.root == node
        ensures fresh(node)
        ensures Br' == Br + {node}
    {
        node := new BSTNode(k);
        Br' := Br + {node};
    }

    method Set_k(ghost Br: set<BSTNode>, k: int)
        returns (ghost Br': set<BSTNode>)
        modifies this
        ensures this.k == k
        ensures this.l == old(this.l)
        ensures this.r == old(this.r)
        ensures this.p == old(this.p)
        ensures this.min == old(this.min)
        ensures this.max == old(this.max)
        ensures this.keys == old(this.keys)
        ensures this.repr == old(this.repr)
        ensures this.root == old(this.root)
        ensures this.depth == old(this.depth)
        ensures this.p == null ==> Br' == Br + {this}
        ensures this.p != null ==> Br' == Br + {this, this.p}
    {
        Br' := Br;
        this.k := k;
        Br' := Br' + {this};
        if this.p != null {
            Br' := Br' + {this.p};
        }
    }

    method Set_l(ghost Br: set<BSTNode>, l: BSTNode?)
        returns (ghost Br': set<BSTNode>)
        modifies this
        ensures this.k == old(this.k)
        ensures this.l == l
        ensures this.r == old(this.r)
        ensures this.p == old(this.p)
        ensures this.min == old(this.min)
        ensures this.max == old(this.max)
        ensures this.keys == old(this.keys)
        ensures this.repr == old(this.repr)
        ensures this.root == old(this.root)
        ensures this.depth == old(this.depth)
        ensures old(this.l) == null ==> Br' == Br + {this}
        ensures old(this.l) != null ==> Br' == Br + {this, old(this.l)}
    {
        Br' := Br;
        if this.l != null {
            Br' := Br' + {this.l};
        }
        this.l := l;
        Br' := Br' + {this};
    }

    method Set_r(ghost Br: set<BSTNode>, r: BSTNode?)
        returns (ghost Br': set<BSTNode>)
        modifies this
        ensures this.k == old(this.k)
        ensures this.l == old(this.l)
        ensures this.r == r
        ensures this.p == old(this.p)
        ensures this.min == old(this.min)
        ensures this.max == old(this.max)
        ensures this.keys == old(this.keys)
        ensures this.repr == old(this.repr)
        ensures this.root == old(this.root)
        ensures this.depth == old(this.depth)
        ensures old(this.r) == null ==> Br' == Br + {this}
        ensures old(this.r) != null ==> Br' == Br + {this, old(this.r)}
    {
        Br' := Br;
        if this.r != null {
            Br' := Br' + {this.r};
        }
        this.r := r;
        Br' := Br' + {this};
    }

    method Set_p(ghost Br: set<BSTNode>, p: BSTNode?)
        returns (ghost Br': set<BSTNode>)
        requires this.p != null
        modifies this
        ensures this.k == old(this.k)
        ensures this.l == old(this.l)
        ensures this.r == old(this.r)
        ensures this.p == p
        ensures this.min == old(this.min)
        ensures this.max == old(this.max)
        ensures this.keys == old(this.keys)
        ensures this.repr == old(this.repr)
        ensures this.root == old(this.root)
        ensures this.depth == old(this.depth)
        ensures old(this.p) == null ==> Br' == Br + {this}
        ensures old(this.p) != null ==> Br' == Br + {this, old(this.p)}
    {
        Br' := Br;
        if this.p != null {
            Br' := Br' + {this.p};
        }
        this.p := p;
        Br' := Br' + {this};
    }

    ghost method Set_min(Br: set<BSTNode>, min: int)
        returns (Br': set<BSTNode>)
        modifies this
        ensures this.k == old(this.k)
        ensures this.l == old(this.l)
        ensures this.r == old(this.r)
        ensures this.p == old(this.p)
        ensures this.min == min
        ensures this.max == old(this.max)
        ensures this.keys == old(this.keys)
        ensures this.repr == old(this.repr)
        ensures this.root == old(this.root)
        ensures this.depth == old(this.depth)
        ensures this.p == null ==> Br' == Br + {this}
        ensures this.p != null ==> Br' == Br + {this, this.p}
    {
        Br' := Br;
        this.min := min;
        Br' := Br' + {this};
        if this.p != null {
            Br' := Br' + {this.p};
        }
    }

    ghost method Set_max(Br: set<BSTNode>, max: int)
        returns (Br': set<BSTNode>)
        modifies this
        ensures this.k == old(this.k)
        ensures this.l == old(this.l)
        ensures this.r == old(this.r)
        ensures this.p == old(this.p)
        ensures this.min == old(this.min)
        ensures this.max == max
        ensures this.keys == old(this.keys)
        ensures this.repr == old(this.repr)
        ensures this.root == old(this.root)
        ensures this.depth == old(this.depth)
        ensures this.p == null ==> Br' == Br + {this}
        ensures this.p != null ==> Br' == Br + {this, this.p}
    {
        Br' := Br;
        this.max := max;
        Br' := Br' + {this};
        if this.p != null {
            Br' := Br' + {this.p};
        }
    }

    ghost method Set_keys(Br: set<BSTNode>, keys: set<int>)
        returns (Br': set<BSTNode>)
        modifies this
        ensures this.k == old(this.k)
        ensures this.l == old(this.l)
        ensures this.r == old(this.r)
        ensures this.p == old(this.p)
        ensures this.min == old(this.min)
        ensures this.max == old(this.max)
        ensures this.keys == keys
        ensures this.repr == old(this.repr)
        ensures this.root == old(this.root)
        ensures this.depth == old(this.depth)
        ensures this.p == null ==> Br' == Br + {this}
        ensures this.p != null ==> Br' == Br + {this, this.p}
    {
        Br' := Br;
        this.keys := keys;
        Br' := Br' + {this};
        if this.p != null {
            Br' := Br' + {this.p};
        }
    }

    ghost method Set_repr(Br: set<BSTNode>, repr: set<BSTNode>)
        returns (Br': set<BSTNode>)
        requires this.p != null
        modifies this
        ensures this.k == old(this.k)
        ensures this.l == old(this.l)
        ensures this.r == old(this.r)
        ensures this.p == old(this.p)
        ensures this.min == old(this.min)
        ensures this.max == old(this.max)
        ensures this.keys == old(this.keys)
        ensures this.repr == repr
        ensures this.root == old(this.root)
        ensures this.depth == old(this.depth)
        ensures this.p == null ==> Br' == Br + {this}
        ensures this.p != null ==> Br' == Br + {this, this.p}
    {
        Br' := Br;
        this.repr := repr;
        Br' := Br' + {this};
        if this.p != null {
            Br' := Br' + {this.p};
        }
    }

    ghost method Set_root(Br: set<BSTNode>, root: BSTNode)
        returns (Br': set<BSTNode>)
        requires this.p != null
        modifies this
        ensures this.k == old(this.k)
        ensures this.l == old(this.l)
        ensures this.r == old(this.r)
        ensures this.p == old(this.p)
        ensures this.min == old(this.min)
        ensures this.max == old(this.max)
        ensures this.keys == old(this.keys)
        ensures this.repr == old(this.repr)
        ensures this.root == root
        ensures this.depth == old(this.depth)
        ensures Br' == Br + {this} + (if this.l == null then {} else {this.l})
                            + (if this.r == null then {} else {this.r})
    {
        Br' := Br;
        this.root := root;
        Br' := Br' + {this};
        Br' := Br' + (if this.l == null then {} else {this.l})
                    + (if this.r == null then {} else {this.r});
    }

    ghost method Set_depth(Br: set<BSTNode>, depth: nat)
        returns (Br': set<BSTNode>)
        requires this.p != null
        modifies this
        ensures this.k == old(this.k)
        ensures this.l == old(this.l)
        ensures this.r == old(this.r)
        ensures this.p == old(this.p)
        ensures this.min == old(this.min)
        ensures this.max == old(this.max)
        ensures this.keys == old(this.keys)
        ensures this.repr == old(this.repr)
        ensures this.root == old(this.root)
        ensures this.depth == depth
        ensures Br' == Br + {this} + (if this.l == null then {} else {this.l})
                            + (if this.r == null then {} else {this.r})
    {
        Br' := Br;
        this.depth := depth;
        Br' := Br' + {this};
        Br' := Br' + (if this.l == null then {} else {this.l})
                    + (if this.r == null then {} else {this.r});
    }

    ghost method DeleteFromRootRepr(Br: set<BSTNode>, node: BSTNode)
        returns (Br': set<BSTNode>)
        requires this.p == null
        requires node.Isolated()
        modifies this
        ensures this.k == old(this.k)
        ensures this.l == old(this.l)
        ensures this.r == old(this.r)
        ensures this.p == old(this.p)
        ensures this.min == old(this.min)
        ensures this.max == old(this.max)
        ensures this.keys == old(this.keys)
        ensures this.repr == old(this.repr) - {node}
        ensures this.root == old(this.root)
        ensures this.depth == old(this.depth)
        ensures Br' == Br + {this}
    {
        Br' := Br;
        this.repr := this.repr - {node};
        Br' := Br' + {this};
    }
}

lemma {:axiom} IfNotBr_ThenLC(Br: set<BSTNode>, x: BSTNode?)
    ensures x != null && x !in Br ==> x.LC()

ghost method AssertLCAndRemove(Br: set<BSTNode>, x: BSTNode?)
    returns (Br': set<BSTNode>)
    ensures (x != null && x.LC()) ==> Br' == Br - {x}
    ensures (x == null || !x.LC()) ==> Br' == Br
{
    if x != null && x.LC() {
        Br' := Br - {x};
    } else {
        Br' := Br;
    }
}
