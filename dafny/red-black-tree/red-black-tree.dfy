// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions"
// by Adithya Murali, Cody Rivera, and P. Madhusudan.
// 
// Artifact by Cody Rivera, 2023-2024. 
//
// Definition of red-black trees.

class RBTNode {
    var k: int
    var l: RBTNode?
    var r: RBTNode?
    var p: RBTNode?
    var black: bool
    ghost var min: int
    ghost var max: int
    ghost var keys: set<int>
    ghost var repr: set<RBTNode>
    ghost var black_height: nat

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
        // Special RBT properties
        && (this.l == null && this.r == null ==>
                this.black_height == (if this.black then 1 else 0))
        && (this.l != null && this.r == null ==>
                this.black_height == (if this.black then 1 else 0)
                && this.l.black_height == 0
                && (this.black || this.l.black))
        && (this.l == null && this.r != null ==>
                this.black_height == (if this.black then 1 else 0)
                && this.r.black_height == 0
                && (this.black || this.r.black))
        && (this.l != null && this.r != null ==>
                (this.l.black_height > this.r.black_height ==>
                    this.black_height == (if this.black then this.l.black_height + 1 else this.l.black_height))
                && (this.l.black_height <= this.r.black_height ==>
                        this.black_height == (if this.black then this.r.black_height + 1 else this.r.black_height))
                && this.l.black_height == this.r.black_height
                && (this.black || (this.l.black && this.r.black)))
    }

    ghost predicate LC_Trans_RedRed()
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
        // Special RBT properties
        && (this.l == null && this.r == null ==>
                this.black_height == (if this.black then 1 else 0))
        && (this.l != null && this.r == null ==>
                this.black_height == (if this.black then 1 else 0)
                && this.l.black_height == 0)
        && (this.l == null && this.r != null ==>
                this.black_height == (if this.black then 1 else 0)
                && this.r.black_height == 0)
        && (this.l != null && this.r != null ==>
                (this.l.black_height > this.r.black_height ==>
                    this.black_height == (if this.black then this.l.black_height + 1 else this.l.black_height))
                && (this.l.black_height <= this.r.black_height ==>
                        this.black_height == (if this.black then this.r.black_height + 1 else this.r.black_height))
                && this.l.black_height == this.r.black_height)
    }

    ghost predicate LC_Trans_DoubleBlack()
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
        // Special RBT properties
        && (this.l == null && this.r == null ==>
                this.black_height == (if this.black then 1 else 0))
        && (this.l != null && this.r == null ==>
                this.black_height == (if this.black then 1 + this.l.black_height else this.l.black_height)
                && this.l.black_height <= 1
                && (this.black || this.l.black))
        && (this.l == null && this.r != null ==>
                this.black_height == (if this.black then 1 + this.r.black_height else this.r.black_height)
                && this.r.black_height <= 1
                && (this.black || this.r.black))
        && (this.l != null && this.r != null ==>
                (this.l.black_height > this.r.black_height ==>
                    this.black_height == (if this.black then this.l.black_height + 1 else this.l.black_height))
                && (this.l.black_height <= this.r.black_height ==>
                        this.black_height == (if this.black then this.r.black_height + 1 else this.r.black_height))
                && (this.l.black_height == this.r.black_height
                    || this.l.black_height + 1 == this.r.black_height
                    || this.l.black_height == this.r.black_height + 1)
                && (this.black || (this.l.black && this.r.black)))
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
    static method Create(ghost Br: set<RBTNode>, k: int)
        returns (ghost Br': set<RBTNode>, node: RBTNode)
        ensures node.k == k
        ensures node.l == null
        ensures node.r == null
        ensures node.p == null
        ensures fresh(node)
        ensures Br' == Br + {node}
    {
        node := new RBTNode(k);
        Br' := Br + {node};
    }

    method Set_k(ghost Br: set<RBTNode>, k: int)
        returns (ghost Br': set<RBTNode>)
        modifies this
        ensures this.k == k
        ensures this.l == old(this.l)
        ensures this.r == old(this.r)
        ensures this.p == old(this.p)
        ensures this.min == old(this.min)
        ensures this.max == old(this.max)
        ensures this.keys == old(this.keys)
        ensures this.repr == old(this.repr)
        ensures this.black == old(this.black)
        ensures this.black_height == old(this.black_height)
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

    method Set_l(ghost Br: set<RBTNode>, l: RBTNode?)
        returns (ghost Br': set<RBTNode>)
        modifies this
        ensures this.k == old(this.k)
        ensures this.l == l
        ensures this.r == old(this.r)
        ensures this.p == old(this.p)
        ensures this.min == old(this.min)
        ensures this.max == old(this.max)
        ensures this.keys == old(this.keys)
        ensures this.repr == old(this.repr)
        ensures this.black == old(this.black)
        ensures this.black_height == old(this.black_height)
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

    method Set_r(ghost Br: set<RBTNode>, r: RBTNode?)
        returns (ghost Br': set<RBTNode>)
        modifies this
        ensures this.k == old(this.k)
        ensures this.l == old(this.l)
        ensures this.r == r
        ensures this.p == old(this.p)
        ensures this.min == old(this.min)
        ensures this.max == old(this.max)
        ensures this.keys == old(this.keys)
        ensures this.repr == old(this.repr)
        ensures this.black == old(this.black)
        ensures this.black_height == old(this.black_height)
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

    method Set_p(ghost Br: set<RBTNode>, p: RBTNode?)
        returns (ghost Br': set<RBTNode>)
        modifies this
        ensures this.k == old(this.k)
        ensures this.l == old(this.l)
        ensures this.r == old(this.r)
        ensures this.p == p
        ensures this.min == old(this.min)
        ensures this.max == old(this.max)
        ensures this.keys == old(this.keys)
        ensures this.repr == old(this.repr)
        ensures this.black == old(this.black)
        ensures this.black_height == old(this.black_height)
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

    ghost method Set_min(Br: set<RBTNode>, min: int)
        returns (Br': set<RBTNode>)
        modifies this
        ensures this.k == old(this.k)
        ensures this.l == old(this.l)
        ensures this.r == old(this.r)
        ensures this.p == old(this.p)
        ensures this.min == min
        ensures this.max == old(this.max)
        ensures this.keys == old(this.keys)
        ensures this.repr == old(this.repr)
        ensures this.black == old(this.black)
        ensures this.black_height == old(this.black_height)
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

    ghost method Set_max(Br: set<RBTNode>, max: int)
        returns (Br': set<RBTNode>)
        modifies this
        ensures this.k == old(this.k)
        ensures this.l == old(this.l)
        ensures this.r == old(this.r)
        ensures this.p == old(this.p)
        ensures this.min == old(this.min)
        ensures this.max == max
        ensures this.keys == old(this.keys)
        ensures this.repr == old(this.repr)
        ensures this.black == old(this.black)
        ensures this.black_height == old(this.black_height)
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

    ghost method Set_keys(Br: set<RBTNode>, keys: set<int>)
        returns (Br': set<RBTNode>)
        modifies this
        ensures this.k == old(this.k)
        ensures this.l == old(this.l)
        ensures this.r == old(this.r)
        ensures this.p == old(this.p)
        ensures this.min == old(this.min)
        ensures this.max == old(this.max)
        ensures this.keys == keys
        ensures this.repr == old(this.repr)
        ensures this.black == old(this.black)
        ensures this.black_height == old(this.black_height)
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

    ghost method Set_repr(Br: set<RBTNode>, repr: set<RBTNode>)
        returns (Br': set<RBTNode>)
        modifies this
        ensures this.k == old(this.k)
        ensures this.l == old(this.l)
        ensures this.r == old(this.r)
        ensures this.p == old(this.p)
        ensures this.min == old(this.min)
        ensures this.max == old(this.max)
        ensures this.keys == old(this.keys)
        ensures this.repr == repr
        ensures this.black == old(this.black)
        ensures this.black_height == old(this.black_height)
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

    method Set_black(ghost Br: set<RBTNode>, black: bool)
        returns (ghost Br': set<RBTNode>)
        modifies this
        ensures this.k == old(this.k)
        ensures this.l == old(this.l)
        ensures this.r == old(this.r)
        ensures this.p == old(this.p)
        ensures this.min == old(this.min)
        ensures this.max == old(this.max)
        ensures this.keys == old(this.keys)
        ensures this.repr == old(this.repr)
        ensures this.black == black
        ensures this.black_height == old(this.black_height)
        ensures this.p == null ==> Br' == Br + {this}
        ensures this.p != null ==> Br' == Br + {this, this.p}
    {
        Br' := Br;
        this.black := black;
        Br' := Br' + {this};
        if this.p != null {
            Br' := Br' + {this.p};
        }
    }

    ghost method Set_black_height(Br: set<RBTNode>, black_height: nat)
        returns (Br': set<RBTNode>)
        modifies this
        ensures this.k == old(this.k)
        ensures this.l == old(this.l)
        ensures this.r == old(this.r)
        ensures this.p == old(this.p)
        ensures this.min == old(this.min)
        ensures this.max == old(this.max)
        ensures this.keys == old(this.keys)
        ensures this.repr == old(this.repr)
        ensures this.black == old(this.black)
        ensures this.black_height == black_height
        ensures this.p == null ==> Br' == Br + {this}
        ensures this.p != null ==> Br' == Br + {this, this.p}
    {
        Br' := Br;
        this.black_height := black_height;
        Br' := Br' + {this};
        if this.p != null {
            Br' := Br' + {this.p};
        }
    }
}

lemma {:axiom} IfNotBr_ThenLC(Br: set<RBTNode>, x: RBTNode?)
    ensures x != null && x !in Br ==> x.LC()

ghost method AssertLCAndRemove(Br: set<RBTNode>, x: RBTNode?)
    returns (Br': set<RBTNode>)
    ensures (x != null && x.LC()) ==> Br' == Br - {x}
    ensures (x == null || !x.LC()) ==> Br' == Br
{
    if x != null && x.LC() {
        Br' := Br - {x};
    } else {
        Br' := Br;
    }
}
