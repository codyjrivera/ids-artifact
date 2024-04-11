// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions"
// by Adithya Murali, Cody Rivera, and P. Madhusudan.
// 
// Artifact by Cody Rivera, 2023-2024. 
//
// Data structure definition of AVL trees.

class AVLNode {
    var k: int
    var l: AVLNode?
    var r: AVLNode?
    var p: AVLNode?
    var height: nat
    ghost var min: int
    ghost var max: int
    ghost var keys: set<int>
    ghost var repr: set<AVLNode>

    constructor (k: int) 
        ensures this.k == k 
        ensures this.l == null
        ensures this.r == null
        ensures this.p == null
    {
        this.k := k;
        this.l := null;
        this.r := null;
        this.p := null;
    }

    ghost predicate LC()
        reads this, this.p, this.l, this.r, this.repr
    {
        this in this.repr
        && this.min <= this.k <= this.max
        && (this.p != null ==>
                this.p !in this.repr
                && (this.p.l == this || this.p.r == this))
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
        // Special AVL properties
        && this.height >= 1
        && (this.l == null && this.r == null ==>
                this.height == 1)
        && (this.l != null && this.r == null ==>
                this.height == this.l.height + 1
                && this.l.height == 1)
        && (this.l == null && this.r != null ==>
                this.height == this.r.height + 1
                && this.r.height == 1)
        && (this.l != null && this.r != null ==>
                (this.l.height > this.r.height ==>
                    this.height == this.l.height + 1)
                && (this.l.height <= this.r.height ==>
                        this.height == this.r.height + 1)
                && -1 <= this.r.height - this.l.height <= 1)
    }

    ghost predicate LC_Trans_Unbalanced()
        reads this, this.p, this.l, this.r, this.repr
    {
        this in this.repr
        && this.min <= this.k <= this.max
        && (this.p != null ==>
                this.p !in this.repr
                && (this.p.l == this || this.p.r == this))
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
        // Special AVL properties
        && this.height >= 1
        && (this.l == null && this.r == null ==>
                this.height == 1)
        && (this.l != null && this.r == null ==>
                this.height == this.l.height + 1
                && this.l.height <= 2)
        && (this.l == null && this.r != null ==>
                this.height == this.r.height + 1
                && this.r.height <= 2)
        && (this.l != null && this.r != null ==>
                (this.l.height > this.r.height ==>
                    this.height == this.l.height + 1)
                && (this.l.height <= this.r.height ==>
                        this.height == this.r.height + 1)
                && -2 <= this.r.height - this.l.height <= 2)
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
    static method Create(ghost Br: set<AVLNode>, k: int)
        returns (ghost Br': set<AVLNode>, node: AVLNode)
        ensures node.k == k
        ensures node.l == null
        ensures node.r == null
        ensures node.p == null
        ensures fresh(node)
        ensures Br' == Br + {node}
    {
        node := new AVLNode(k);
        Br' := Br + {node};
    }

    method Set_k(ghost Br: set<AVLNode>, k: int)
        returns (ghost Br': set<AVLNode>)
        modifies this
        ensures this.k == k
        ensures this.l == old(this.l)
        ensures this.r == old(this.r)
        ensures this.p == old(this.p)
        ensures this.min == old(this.min)
        ensures this.max == old(this.max)
        ensures this.keys == old(this.keys)
        ensures this.repr == old(this.repr)
        ensures this.height == old(this.height)
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

    method Set_l(ghost Br: set<AVLNode>, l: AVLNode?)
        returns (ghost Br': set<AVLNode>)
        modifies this
        ensures this.k == old(this.k)
        ensures this.l == l
        ensures this.r == old(this.r)
        ensures this.p == old(this.p)
        ensures this.min == old(this.min)
        ensures this.max == old(this.max)
        ensures this.keys == old(this.keys)
        ensures this.repr == old(this.repr)
        ensures this.height == old(this.height)
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

    method Set_r(ghost Br: set<AVLNode>, r: AVLNode?)
        returns (ghost Br': set<AVLNode>)
        modifies this
        ensures this.k == old(this.k)
        ensures this.l == old(this.l)
        ensures this.r == r
        ensures this.p == old(this.p)
        ensures this.min == old(this.min)
        ensures this.max == old(this.max)
        ensures this.keys == old(this.keys)
        ensures this.repr == old(this.repr)

        ensures this.height == old(this.height)
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

    method Set_p(ghost Br: set<AVLNode>, p: AVLNode?)
        returns (ghost Br': set<AVLNode>)
        modifies this
        ensures this.k == old(this.k)
        ensures this.l == old(this.l)
        ensures this.r == old(this.r)
        ensures this.p == p
        ensures this.min == old(this.min)
        ensures this.max == old(this.max)
        ensures this.keys == old(this.keys)
        ensures this.repr == old(this.repr)

        ensures this.height == old(this.height)
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

    ghost method Set_min(Br: set<AVLNode>, min: int)
        returns (Br': set<AVLNode>)
        modifies this
        ensures this.k == old(this.k)
        ensures this.l == old(this.l)
        ensures this.r == old(this.r)
        ensures this.p == old(this.p)
        ensures this.min == min
        ensures this.max == old(this.max)
        ensures this.keys == old(this.keys)
        ensures this.repr == old(this.repr)

        ensures this.height == old(this.height)
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

    ghost method Set_max(Br: set<AVLNode>, max: int)
        returns (Br': set<AVLNode>)
        modifies this
        ensures this.k == old(this.k)
        ensures this.l == old(this.l)
        ensures this.r == old(this.r)
        ensures this.p == old(this.p)
        ensures this.min == old(this.min)
        ensures this.max == max
        ensures this.keys == old(this.keys)
        ensures this.repr == old(this.repr)

        ensures this.height == old(this.height)
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

    ghost method Set_keys(Br: set<AVLNode>, keys: set<int>)
        returns (Br': set<AVLNode>)
        modifies this
        ensures this.k == old(this.k)
        ensures this.l == old(this.l)
        ensures this.r == old(this.r)
        ensures this.p == old(this.p)
        ensures this.min == old(this.min)
        ensures this.max == old(this.max)
        ensures this.keys == keys
        ensures this.repr == old(this.repr)

        ensures this.height == old(this.height)
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

    ghost method Set_repr(Br: set<AVLNode>, repr: set<AVLNode>)
        returns (Br': set<AVLNode>)
        modifies this
        ensures this.k == old(this.k)
        ensures this.l == old(this.l)
        ensures this.r == old(this.r)
        ensures this.p == old(this.p)
        ensures this.min == old(this.min)
        ensures this.max == old(this.max)
        ensures this.keys == old(this.keys)
        ensures this.repr == repr

        ensures this.height == old(this.height)
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

    method Set_height(ghost Br: set<AVLNode>, height: nat)
        returns (ghost Br': set<AVLNode>)
        modifies this
        ensures this.k == old(this.k)
        ensures this.l == old(this.l)
        ensures this.r == old(this.r)
        ensures this.p == old(this.p)
        ensures this.min == old(this.min)
        ensures this.max == old(this.max)
        ensures this.keys == old(this.keys)
        ensures this.repr == old(this.repr)

        ensures this.height == height
        ensures this.p == null ==> Br' == Br + {this}
        ensures this.p != null ==> Br' == Br + {this, this.p}
    {
        Br' := Br;
        this.height := height;
        Br' := Br' + {this};
        if this.p != null {
            Br' := Br' + {this.p};
        }
    }
}

lemma {:axiom} IfNotBr_ThenLC(Br: set<AVLNode>, x: AVLNode?)
    ensures x != null && x !in Br ==> x.LC()

ghost method AssertLCAndRemove(Br: set<AVLNode>, x: AVLNode?)
    returns (Br': set<AVLNode>)
    ensures (x != null && x.LC()) ==> Br' == Br - {x}
    ensures (x == null || !x.LC()) ==> Br' == Br
{
    if x != null && x.LC() {
        Br' := Br - {x};
    } else {
        Br' := Br;
    }
}
