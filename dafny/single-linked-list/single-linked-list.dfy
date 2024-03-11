// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions"
// by Anonymous Authors.
// 
// Artifact by Anonymous Author, 2023. 
//
// Definition of the singly-linked list data structure.

class SLLNode {
    var k: int
    var next: SLLNode?
    ghost var prev: SLLNode?
    ghost var keys: set<int>
    ghost var repr: set<SLLNode>

    constructor (k: int) 
        ensures this.k == k 
        ensures this.next == null
        ensures this.prev == null
    {
        this.k := k;
        this.next := null;
        this.prev := null;
    }

    ghost predicate LC()
        reads this, this.next, this.prev, this.repr
    {
        this in this.repr
        && (this.prev != null ==>
                this.prev !in this.repr
                && this.prev.next == this)
        && (this.next == null ==>
                this.keys == {this.k}
                && this.repr == {this})
        && (this.next != null ==> 
                this.next in this.repr
                && this !in this.next.repr
                && this.repr == {this} + this.next.repr
                && this.keys == {this.k} + this.next.keys
                && this.next.prev == this)
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
    static method Create(ghost Br: set<SLLNode>, k: int)
        returns (ghost Br': set<SLLNode>, node: SLLNode)
        ensures node.k == k
        ensures node.next == null
        ensures node.prev == null
        ensures fresh(node)
        ensures Br' == Br + {node}
    {
        node := new SLLNode(k);
        Br' := Br + {node};
    }

    method Set_k(ghost Br: set<SLLNode>, k: int)
        returns (ghost Br': set<SLLNode>)
        modifies this
        ensures this.k == k
        ensures this.next == old(this.next)
        ensures this.prev == old(this.prev)
        ensures this.keys == old(this.keys)
        ensures this.repr == old(this.repr)
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

    method Set_next(ghost Br: set<SLLNode>, next: SLLNode?)
        returns (ghost Br': set<SLLNode>)
        modifies this
        ensures this.k == old(this.k)
        ensures this.next == next
        ensures this.prev == old(this.prev)
        ensures this.keys == old(this.keys)
        ensures this.repr == old(this.repr)
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

    method Set_prev(ghost Br: set<SLLNode>, prev: SLLNode?)
        returns (ghost Br': set<SLLNode>)
        modifies this
        ensures this.k == old(this.k)
        ensures this.next == old(this.next)
        ensures this.prev == prev
        ensures this.keys == old(this.keys)
        ensures this.repr == old(this.repr)
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

    ghost method Set_keys(Br: set<SLLNode>, keys: set<int>)
        returns (Br': set<SLLNode>)
        modifies this
        ensures this.k == old(this.k)
        ensures this.next == old(this.next)
        ensures this.prev == old(this.prev)
        ensures this.keys == keys
        ensures this.repr == old(this.repr)
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

    ghost method Set_repr(Br: set<SLLNode>, repr: set<SLLNode>)
        returns (Br': set<SLLNode>)
        modifies this
        ensures this.k == old(this.k)
        ensures this.next == old(this.next)
        ensures this.prev == old(this.prev)
        ensures this.keys == old(this.keys)
        ensures this.repr == repr
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
}

lemma {:axiom} IfNotBr_ThenLC(Br: set<SLLNode>, x: SLLNode?)
    ensures x != null && x !in Br ==> x.LC()

ghost method AssertLCAndRemove(Br: set<SLLNode>, x: SLLNode?)
    returns (Br': set<SLLNode>)
    ensures (x != null && x.LC()) ==> Br' == Br - {x}
    ensures (x == null || !x.LC()) ==> Br' == Br
{
    if x != null && x.LC() {
        Br' := Br - {x};
    } else {
        Br' := Br;
    }
}
