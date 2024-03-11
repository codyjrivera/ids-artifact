// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions"
// by Anonymous Authors.
// 
// Artifact by Anonymous Author, 2023. 
//
// Definition of the treap data structure.

class TreapNode {
    var k: int
    var prio: int
    var l: TreapNode?
    var r: TreapNode?
    var p: TreapNode?
    ghost var min: int
    ghost var max: int
    ghost var keys: set<int>
    ghost var repr: set<TreapNode>

    constructor (k: int, prio: int) 
        ensures this.k == k
        ensures this.prio == prio
        ensures this.l == null
        ensures this.r == null
        ensures this.p == null
    {
        this.k := k;
        this.prio := prio;
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
                && this.l.max < this.k
                && this.l.prio <= this.prio)
        && (this.r != null ==> 
                this.r in this.repr
                && this !in this.r.repr
                && this.r.p == this
                && this.r.min > this.k
                && this.r.prio <= this.prio)
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
    static method Create(ghost Br: set<TreapNode>, k: int, prio: int)
        returns (ghost Br': set<TreapNode>, node: TreapNode)
        ensures node.k == k
        ensures node.l == null
        ensures node.r == null
        ensures node.p == null
        ensures fresh(node)
        ensures Br' == Br + {node}
    {
        node := new TreapNode(k, prio);
        Br' := Br + {node};
    }

    method Set_k(ghost Br: set<TreapNode>, k: int)
        returns (ghost Br': set<TreapNode>)
        modifies this
        ensures this.k == k
        ensures this.prio == old(this.prio)
        ensures this.l == old(this.l)
        ensures this.r == old(this.r)
        ensures this.p == old(this.p)
        ensures this.min == old(this.min)
        ensures this.max == old(this.max)
        ensures this.keys == old(this.keys)
        ensures this.repr == old(this.repr)
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

    method Set_prio(ghost Br: set<TreapNode>, prio: int)
        returns (ghost Br': set<TreapNode>)
        modifies this
        ensures this.k == old(this.k)
        ensures this.prio == prio
        ensures this.l == old(this.l)
        ensures this.r == old(this.r)
        ensures this.p == old(this.p)
        ensures this.min == old(this.min)
        ensures this.max == old(this.max)
        ensures this.keys == old(this.keys)
        ensures this.repr == old(this.repr)
        ensures this.p == null ==> Br' == Br + {this}
        ensures this.p != null ==> Br' == Br + {this, this.p}
    {
        Br' := Br;
        this.prio := prio;
        Br' := Br' + {this};
        if this.p != null {
            Br' := Br' + {this.p};
        }
    }

    method Set_l(ghost Br: set<TreapNode>, l: TreapNode?)
        returns (ghost Br': set<TreapNode>)
        modifies this
        ensures this.k == old(this.k)
        ensures this.prio == old(this.prio)
        ensures this.l == l
        ensures this.r == old(this.r)
        ensures this.p == old(this.p)
        ensures this.min == old(this.min)
        ensures this.max == old(this.max)
        ensures this.keys == old(this.keys)
        ensures this.repr == old(this.repr)
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

    method Set_r(ghost Br: set<TreapNode>, r: TreapNode?)
        returns (ghost Br': set<TreapNode>)
        modifies this
        ensures this.k == old(this.k)
        ensures this.prio == old(this.prio)
        ensures this.l == old(this.l)
        ensures this.r == r
        ensures this.p == old(this.p)
        ensures this.min == old(this.min)
        ensures this.max == old(this.max)
        ensures this.keys == old(this.keys)
        ensures this.repr == old(this.repr)
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

    method Set_p(ghost Br: set<TreapNode>, p: TreapNode?)
        returns (ghost Br': set<TreapNode>)
        modifies this
        ensures this.k == old(this.k)
        ensures this.prio == old(this.prio)
        ensures this.l == old(this.l)
        ensures this.r == old(this.r)
        ensures this.p == p
        ensures this.min == old(this.min)
        ensures this.max == old(this.max)
        ensures this.keys == old(this.keys)
        ensures this.repr == old(this.repr)
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

    ghost method Set_min(Br: set<TreapNode>, min: int)
        returns (Br': set<TreapNode>)
        modifies this
        ensures this.k == old(this.k)
        ensures this.prio == old(this.prio)
        ensures this.l == old(this.l)
        ensures this.r == old(this.r)
        ensures this.p == old(this.p)
        ensures this.min == min
        ensures this.max == old(this.max)
        ensures this.keys == old(this.keys)
        ensures this.repr == old(this.repr)
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

    ghost method Set_max(Br: set<TreapNode>, max: int)
        returns (Br': set<TreapNode>)
        modifies this
        ensures this.k == old(this.k)
        ensures this.prio == old(this.prio)
        ensures this.l == old(this.l)
        ensures this.r == old(this.r)
        ensures this.p == old(this.p)
        ensures this.min == old(this.min)
        ensures this.max == max
        ensures this.keys == old(this.keys)
        ensures this.repr == old(this.repr)
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

    ghost method Set_keys(Br: set<TreapNode>, keys: set<int>)
        returns (Br': set<TreapNode>)
        modifies this
        ensures this.k == old(this.k)
        ensures this.prio == old(this.prio)
        ensures this.l == old(this.l)
        ensures this.r == old(this.r)
        ensures this.p == old(this.p)
        ensures this.min == old(this.min)
        ensures this.max == old(this.max)
        ensures this.keys == keys
        ensures this.repr == old(this.repr)
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

    ghost method Set_repr(Br: set<TreapNode>, repr: set<TreapNode>)
        returns (Br': set<TreapNode>)
        modifies this
        ensures this.k == old(this.k)
        ensures this.prio == old(this.prio)
        ensures this.l == old(this.l)
        ensures this.r == old(this.r)
        ensures this.p == old(this.p)
        ensures this.min == old(this.min)
        ensures this.max == old(this.max)
        ensures this.keys == old(this.keys)
        ensures this.repr == repr
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
}

lemma {:axiom} IfNotBr_ThenLC(Br: set<TreapNode>, x: TreapNode?)
    ensures x != null && x !in Br ==> x.LC()

ghost method AssertLCAndRemove(Br: set<TreapNode>, x: TreapNode?)
    returns (Br': set<TreapNode>)
    ensures (x != null && x.LC()) ==> Br' == Br - {x}
    ensures (x == null || !x.LC()) ==> Br' == Br
{
    if x != null && x.LC() {
        Br' := Br - {x};
    } else {
        Br' := Br;
    }
}
