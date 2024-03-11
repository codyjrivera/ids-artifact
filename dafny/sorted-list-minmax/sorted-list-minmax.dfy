// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions"
// by Anonymous Authors.
// 
// Artifact by Anonymous Author, 2023-2024. 
//
// Definition of the sorted list data structure (w/min and max).

class SortedNode {
    var k: int
    var next: SortedNode?
    ghost var prev: SortedNode?
    ghost var keys: set<int>
    ghost var repr: set<SortedNode>
    ghost var sorted: bool
    ghost var rev_sorted: bool
    ghost var min: int
    ghost var max: int

    constructor (k: int) 
        ensures this.k == k 
    {
        this.k := k;
    }

    ghost predicate LC()
        reads this, this.next, this.prev, this.repr
    {
        this.min <= this.k <= this.max
        && (this.prev != null ==>
                && this.prev !in this.repr
                && this.prev.next == this)
        && (this.next == null ==>
                this.keys == {this.k}
                && this.repr == {this}
                && this.min == this.k
                && this.max == this.k)
        && (this.next != null ==> 
                && this.next in this.repr
                && this !in this.next.repr
                && this.repr == {this} + this.next.repr
                && this.keys == {this.k} + this.next.keys
                && this.next.prev == this
                && (this.rev_sorted ==> this.k >= this.next.k)
                && (this.sorted ==> this.k <= this.next.k)
                && this.rev_sorted == this.next.rev_sorted
                && this.sorted == this.next.sorted
                && this.min == (if this.k <= this.next.min then this.k else this.next.min)
                && this.max == (if this.k >= this.next.max then this.k else this.next.max))
        && !(this.sorted && this.rev_sorted)
    }

    ghost predicate Isolated()
        reads this
    {
        this.next == null && this.prev == null
    }

    /**
    * Data structure manipulation macros.
    * We must prove that these macros update
    * Br correctly.
    */
    static method Create(ghost Br: set<SortedNode>, k: int)
        returns (ghost Br': set<SortedNode>, node: SortedNode)
        ensures node.k == k
        ensures node.next == null
        ensures node.prev == null
        ensures fresh(node)
        ensures Br' == Br + {node}
    {
        node := new SortedNode(k);
        node.prev := null;
        node.next := null;
        Br' := Br + {node};
    }

    method Set_k(ghost Br: set<SortedNode>, k: int)
        returns (ghost Br': set<SortedNode>)
        modifies this
        ensures this.k == k
        ensures this.next == old(this.next)
        ensures this.prev == old(this.prev)
        ensures this.keys == old(this.keys)
        ensures this.repr == old(this.repr)
        ensures this.sorted == old(this.sorted)
        ensures this.rev_sorted == old(this.rev_sorted)
        ensures this.min == old(this.min)
        ensures this.max == old(this.max)
        ensures this.prev == null ==> Br' == Br + {this}
        ensures this.prev != null ==> Br' == Br + {this, this.prev}
    {
        Br' := Br;
        this.k := k;
        Br' := Br' + {this};
        if this.prev != null {
            Br' := Br' + {this.prev};
        }
    }

    method Set_next(ghost Br: set<SortedNode>, next: SortedNode?)
        returns (ghost Br': set<SortedNode>)
        modifies this
        ensures this.k == old(this.k)
        ensures this.next == next
        ensures this.prev == old(this.prev)
        ensures this.keys == old(this.keys)
        ensures this.repr == old(this.repr)
        ensures this.sorted == old(this.sorted)
        ensures this.rev_sorted == old(this.rev_sorted)
        ensures this.min == old(this.min)
        ensures this.max == old(this.max)
        ensures old(this.next) == null ==> Br' == Br + {this}
        ensures old(this.next) != null ==> Br' == Br + {this, old(this.next)}
    {
        Br' := Br;
        if this.next != null {
            Br' := Br' + {this.next};
        }
        this.next := next;
        Br' := Br' + {this};
    }

    ghost method Set_prev(Br: set<SortedNode>, prev: SortedNode?)
        returns (Br': set<SortedNode>)
        modifies this
        ensures this.k == old(this.k)
        ensures this.next == old(this.next)
        ensures this.prev == prev
        ensures this.keys == old(this.keys)
        ensures this.repr == old(this.repr)
        ensures this.sorted == old(this.sorted)
        ensures this.rev_sorted == old(this.rev_sorted)
        ensures this.min == old(this.min)
        ensures this.max == old(this.max)
        ensures old(this.prev) == null ==> Br' == Br + {this}
        ensures old(this.prev) != null ==> Br' == Br + {this, old(this.prev)}
    {
        Br' := Br;
        if this.prev != null {
            Br' := Br' + {this.prev};
        }
        this.prev := prev;
        Br' := Br' + {this};
    }

    ghost method Set_keys(Br: set<SortedNode>, keys: set<int>)
        returns (Br': set<SortedNode>)
        modifies this
        ensures this.k == old(this.k)
        ensures this.next == old(this.next)
        ensures this.prev == old(this.prev)
        ensures this.keys == keys
        ensures this.repr == old(this.repr)
        ensures this.sorted == old(this.sorted)
        ensures this.rev_sorted == old(this.rev_sorted)
        ensures this.min == old(this.min)
        ensures this.max == old(this.max)
        ensures this.prev == null ==> Br' == Br + {this}
        ensures this.prev != null ==> Br' == Br + {this, this.prev}
    {
        Br' := Br;
        this.keys := keys;
        Br' := Br' + {this};
        if this.prev != null {
            Br' := Br' + {this.prev};
        }
    }

    ghost method Set_repr(Br: set<SortedNode>, repr: set<SortedNode>)
        returns (Br': set<SortedNode>)
        modifies this
        ensures this.k == old(this.k)
        ensures this.next == old(this.next)
        ensures this.prev == old(this.prev)
        ensures this.keys == old(this.keys)
        ensures this.repr == repr
        ensures this.sorted == old(this.sorted)
        ensures this.rev_sorted == old(this.rev_sorted)
        ensures this.min == old(this.min)
        ensures this.max == old(this.max)
        ensures this.prev == null ==> Br' == Br + {this}
        ensures this.prev != null ==> Br' == Br + {this, this.prev}
    {
        Br' := Br;
        this.repr := repr;
        Br' := Br' + {this};
        if this.prev != null {
            Br' := Br' + {this.prev};
        }
    }

    ghost method Set_sorted(Br: set<SortedNode>, sorted: bool)
        returns (Br': set<SortedNode>)
        modifies this
        ensures this.k == old(this.k)
        ensures this.next == old(this.next)
        ensures this.prev == old(this.prev)
        ensures this.keys == old(this.keys)
        ensures this.repr == old(this.repr)
        ensures this.sorted == sorted
        ensures this.rev_sorted == old(this.rev_sorted)
        ensures this.min == old(this.min)
        ensures this.max == old(this.max)
        ensures this.prev == null ==> Br' == Br + {this}
        ensures this.prev != null ==> Br' == Br + {this, this.prev}
    {
        Br' := Br;
        this.sorted := sorted;
        Br' := Br' + {this};
        if this.prev != null {
            Br' := Br' + {this.prev};
        }
    }

    ghost method Set_rev_sorted(Br: set<SortedNode>, rev_sorted: bool)
        returns (Br': set<SortedNode>)
        modifies this
        ensures this.k == old(this.k)
        ensures this.next == old(this.next)
        ensures this.prev == old(this.prev)
        ensures this.keys == old(this.keys)
        ensures this.repr == old(this.repr)
        ensures this.sorted == old(this.sorted)
        ensures this.rev_sorted == rev_sorted
        ensures this.min == old(this.min)
        ensures this.max == old(this.max)
        ensures this.prev == null ==> Br' == Br + {this}
        ensures this.prev != null ==> Br' == Br + {this, this.prev}
    {
        Br' := Br;
        this.rev_sorted := rev_sorted;
        Br' := Br' + {this};
        if this.prev != null {
            Br' := Br' + {this.prev};
        }
    }

    ghost method Set_min(Br: set<SortedNode>, min: int)
        returns (Br': set<SortedNode>)
        modifies this
        ensures this.k == old(this.k)
        ensures this.next == old(this.next)
        ensures this.prev == old(this.prev)
        ensures this.keys == old(this.keys)
        ensures this.repr == old(this.repr)
        ensures this.sorted == old(this.sorted)
        ensures this.rev_sorted == old(this.rev_sorted)
        ensures this.min == min
        ensures this.max == old(this.max)
        ensures this.prev == null ==> Br' == Br + {this}
        ensures this.prev != null ==> Br' == Br + {this, this.prev}
    {
        Br' := Br;
        this.min := min;
        Br' := Br' + {this};
        if this.prev != null {
            Br' := Br' + {this.prev};
        }
    }

    ghost method Set_max(Br: set<SortedNode>, max: int)
        returns (Br': set<SortedNode>)
        modifies this
        ensures this.k == old(this.k)
        ensures this.next == old(this.next)
        ensures this.prev == old(this.prev)
        ensures this.keys == old(this.keys)
        ensures this.repr == old(this.repr)
        ensures this.sorted == old(this.sorted)
        ensures this.rev_sorted == old(this.rev_sorted)
        ensures this.min == old(this.min)
        ensures this.max == max
        ensures this.prev == null ==> Br' == Br + {this}
        ensures this.prev != null ==> Br' == Br + {this, this.prev}
    {
        Br' := Br;
        this.max := max;
        Br' := Br' + {this};
        if this.prev != null {
            Br' := Br' + {this.prev};
        }
    }
}

lemma {:axiom} IfNotBr_ThenLC(Br: set<SortedNode>, x: SortedNode?)
    ensures x != null && x !in Br ==> x.LC()

ghost method AssertLCAndRemove(Br: set<SortedNode>, x: SortedNode?)
    returns (Br': set<SortedNode>)
    ensures (x != null && x.LC()) ==> Br' == Br - {x}
    ensures (x == null || !x.LC()) ==> Br' == Br
{
    if x != null && x.LC() {
        Br' := Br - {x};
    } else {
        Br' := Br;
    }
}
