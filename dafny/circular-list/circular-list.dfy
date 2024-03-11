// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions"
// by Anonymous Authors.
// 
// Artifact by Anonymous Author, 2023. 
//
// Definition of the circular list data structure.

class CircularNode {
    var k: int
    var next: CircularNode
    ghost var prev: CircularNode
    ghost var last: CircularNode
    ghost var len: nat
    ghost var rlen: nat
    ghost var keys: set<int>
    ghost var repr: set<CircularNode>


    constructor (k: int) 
        ensures this.k == k
        ensures this.next == this
        ensures this.prev == this
        ensures this.last == this
        ensures this.repr == {this}
    {
        this.k := k;
        this.next := this;
        this.prev := this;
        this.last := this;
        this.repr := {this};
    }

    ghost predicate LC()
        reads *
    {
        && this.prev.next == this
        && this.next.prev == this
        && (this == this.last ==>
                this.len == 0
                && this.rlen == 0
                && this.last == this.next.last
                && (this.next == this ==>
                        this.keys == {}
                        && this.repr == {this})
                && (this.next != this ==>
                        this.keys == this.next.keys
                        && this.repr == {this} + this.next.repr
                        && this !in this.next.repr))
        && (this != this.last ==>
                this.len == this.next.len + 1
                && this.rlen == this.prev.rlen + 1
                && (this.next == this.last ==>
                        this.keys == {this.k}
                        && this.repr == {this})
                && (this.next != this.last ==>
                        this.keys == {this.k} + this.next.keys
                        && this.repr == {this} + this.next.repr
                        && this !in this.next.repr)
                // Special scaffold properties
                && this.last == this.next.last
                && this.last.last == this.last
                && this in this.last.repr 
                && this.prev in this.last.repr 
                && this.next in this.last.repr)
    }

    ghost predicate LC_Trans_MinusNode(n: CircularNode)
        reads *
    {
        && this.prev.next == this
        && this.next.prev == this
        && (this == this.last ==>
                this.len == 0
                && this.rlen == 0
                && this.last == this.next.last
                && (this.next == this ==>
                        this.keys == {}
                        && this.repr == {this})
                && (this.next != this ==>
                        (this.keys == this.next.keys - {n.k}
                            || this.keys == this.next.keys)
                        // We've already updated the Repr
                        && this.repr == {this} + this.next.repr
                        && this !in this.next.repr))
        && (this != this.last ==>
                this.len == this.next.len
                && this.rlen == this.prev.rlen + 1
                && (this.next == this.last ==>
                        this.keys == {this.k}
                        && this.repr == {this})
                && (this.next != this.last ==>
                        (this.keys == ({this.k} + this.next.keys) - {n.k}
                            || this.keys == {this.k} + this.next.keys)
                        && this.repr == ({this} + this.next.repr) - {n}
                        && this !in this.next.repr)
                // Special scaffold properties
                && this.last == this.next.last
                //&& this.last.last == this.last
                && this in this.last.repr 
                && this.prev in this.last.repr 
                && this.next in this.last.repr)
    }

    ghost predicate LC_Trans_PlusNode(n: CircularNode)
        reads *
    {
        && this.prev.next == this
        && this.next.prev == this
        && (this == this.last ==>
                this.len == 0
                && this.rlen == 0
                && this.last == this.next.last
                && (this.next == this ==>
                        this.keys == {}
                        && this.repr == {this})
                && (this.next != this ==>
                        (this.keys == this.next.keys + {n.k}
                            || this.keys == this.next.keys)
                        && this.repr == ({this} + this.next.repr) + {n}
                        && this !in this.next.repr))
        && (this != this.last ==>
                this.len == this.next.len + 2
                && this.rlen == this.prev.rlen + 1
                && (this.next == this.last ==>
                        this.keys == {this.k}
                        && this.repr == {this})
                && (this.next != this.last ==>
                        (this.keys == ({this.k} + this.next.keys) + {n.k}
                            || this.keys == {this.k} + this.next.keys)
                        && this.repr == ({this} + this.next.repr) + {n}
                        && this !in this.next.repr)
                // Special scaffold properties
                && this.last == this.next.last
                //&& this.last.last == this.last
                && this in this.last.repr 
                && this.prev in this.last.repr 
                && this.next in this.last.repr)
    }

    ghost predicate LC_At_Last(n: CircularNode)
        reads *
    {
        && this.prev.next == this
        && this.next.prev == this
        && (this == this.last ==>
                this.len == 0
                && this.rlen == 0
                && this.last == this.next.last
                && (this.next == this ==>
                        this.keys == {}
                        && this.repr == {this})
                && (this.next != this ==>
                        this.keys == this.next.keys
                        && this.repr == {this} + this.next.repr + {n}
                        && this !in this.next.repr))
        && (this != this.last ==>
                this.len == this.next.len + 1
                && this.rlen == this.prev.rlen + 1
                && (this.next == this.last ==>
                        this.keys == {this.k}
                        && this.repr == {this})
                && (this.next != this.last ==>
                        this.keys == {this.k} + this.next.keys
                        && this.repr == {this} + this.next.repr
                        && this !in this.next.repr)
                // Special scaffold properties
                && this.last == this.next.last
                && this.last.last == this.last
                && this in this.last.repr 
                && this.prev in this.last.repr 
                && this.next in this.last.repr)
    }

    ghost predicate LC_Trans_NoRlen()
        reads *
    {
        && this.prev.next == this
        && this.next.prev == this
        && (this == this.last ==>
                this.len == 0
                //&& this.rlen == 0
                && this.last == this.next.last
                && (this.next == this ==>
                        this.keys == {}
                        && this.repr == {this})
                && (this.next != this ==>
                        this.keys == this.next.keys
                        && this.repr == {this} + this.next.repr
                        && this !in this.next.repr))
        && (this != this.last ==>
                this.len == this.next.len + 1
                //&& this.rlen == this.prev.rlen + 1
                && (this.next == this.last ==>
                        this.keys == {this.k}
                        && this.repr == {this})
                && (this.next != this.last ==>
                        this.keys == {this.k} + this.next.keys
                        && this.repr == {this} + this.next.repr
                        && this !in this.next.repr)
                // Special scaffold properties
                && this.last == this.next.last
                && this.last.last == this.last
                && this in this.last.repr 
                && this.prev in this.last.repr 
                && this.next in this.last.repr)
    }

    /**
        * Data structure manipulation macros.
        * We must prove that these macros update
        * Br correctly.
        */
    static method Create(ghost Br: set<CircularNode>, k: int)
        returns (ghost Br': set<CircularNode>, node: CircularNode)
        ensures node.k == k
        ensures node.next == node
        ensures node.prev == node
        ensures node.last == node
        ensures node.repr == {node}
        ensures fresh(node)
        ensures Br' == Br + {node}
    {
        node := new CircularNode(k);
        Br' := Br + {node};
    }

    method Set_k(ghost Br: set<CircularNode>, k: int)
        returns (ghost Br': set<CircularNode>)
        modifies this
        ensures this.k == k
        ensures this.next == old(this.next)
        ensures this.prev == old(this.prev)
        ensures this.last == old(this.last)
        ensures this.len == old(this.len)
        ensures this.rlen == old(this.rlen)
        ensures this.keys == old(this.keys)
        ensures this.repr == old(this.repr)
        ensures Br' == Br + {this, old(this.prev)}
    {
        Br' := Br;
        Br' := Br' + {this.prev};
        this.k := k;
        Br' := Br' + {this};
    }

    method Set_next(ghost Br: set<CircularNode>, next: CircularNode)
        returns (ghost Br': set<CircularNode>)
        modifies this
        ensures this.k == old(this.k)
        ensures this.next == next
        ensures this.prev == old(this.prev)
        ensures this.last == old(this.last)
        ensures this.len == old(this.len)
        ensures this.rlen == old(this.rlen)
        ensures this.keys == old(this.keys)
        ensures this.repr == old(this.repr)
        ensures Br' == Br + {this, old(this.next)}
    {
        Br' := Br;
        Br' := Br' + {this.next};
        this.next := next;
        Br' := Br' + {this};
    }

    ghost method Set_prev(Br: set<CircularNode>, prev: CircularNode)
        returns (Br': set<CircularNode>)
        modifies this
        ensures this.k == old(this.k)
        ensures this.next == old(this.next)
        ensures this.prev == prev
        ensures this.last == old(this.last)
        ensures this.len == old(this.len)
        ensures this.rlen == old(this.rlen)
        ensures this.keys == old(this.keys)
        ensures this.repr == old(this.repr)
        ensures Br' == Br + {this, old(this.prev)}
    {
        Br' := Br;
        Br' := Br' + {this.prev};
        this.prev := prev;
        Br' := Br' + {this};
    }

    ghost method Set_last(Br: set<CircularNode>, last: CircularNode)
        returns (Br': set<CircularNode>)
        requires this.last != this || (this.last == this && this.repr == {this})
        modifies this
        ensures this.k == old(this.k)
        ensures this.next == old(this.next)
        ensures this.prev == old(this.prev)
        ensures this.last == last
        ensures this.len == old(this.len)
        ensures this.rlen == old(this.rlen)
        ensures this.keys == old(this.keys)
        ensures this.repr == old(this.repr)
        ensures Br' == Br + {this, this.next}
    {
        Br' := Br;
        this.last := last;
        Br' := Br' + {this};
        Br' := Br' + {this.next};
    }

    ghost method Set_len(Br: set<CircularNode>, len: nat)
        returns (Br': set<CircularNode>)
        modifies this
        ensures this.k == old(this.k)
        ensures this.next == old(this.next)
        ensures this.prev == old(this.prev)
        ensures this.last == old(this.last)
        ensures this.len == len
        ensures this.rlen == old(this.rlen)
        ensures this.keys == old(this.keys)
        ensures this.repr == old(this.repr)
        ensures Br' == Br + {this, this.prev}
    {
        Br' := Br;
        this.len := len;
        Br' := Br' + {this};
        Br' := Br' + {this.prev};
    }

    ghost method Set_rlen(Br: set<CircularNode>, rlen: nat)
        returns (Br': set<CircularNode>)
        modifies this
        ensures this.k == old(this.k)
        ensures this.next == old(this.next)
        ensures this.prev == old(this.prev)
        ensures this.last == old(this.last)
        ensures this.len == old(this.len)
        ensures this.rlen == rlen
        ensures this.keys == old(this.keys)
        ensures this.repr == old(this.repr)
        ensures Br' == Br + {this, this.next}
        
    {
        Br' := Br;
        this.rlen := rlen;
        Br' := Br' + {this};
        Br' := Br' + {this.next};
    }

    ghost method Set_keys(Br: set<CircularNode>, keys: set<int>)
        returns (Br': set<CircularNode>)
        modifies this
        ensures this.k == old(this.k)
        ensures this.next == old(this.next)
        ensures this.prev == old(this.prev)
        ensures this.last == old(this.last)
        ensures this.len == old(this.len)
        ensures this.rlen == old(this.rlen)
        ensures this.keys == keys
        ensures this.repr == old(this.repr)
        ensures Br' == Br + {this, this.prev}
        
    {
        Br' := Br;
        this.keys := keys;
        Br' := Br' + {this};
        Br' := Br' + {this.prev};
    }

    ghost method Set_repr(Br: set<CircularNode>, repr: set<CircularNode>)
        returns (Br': set<CircularNode>)
        requires this.last != this || (this.last == this && this.repr == {this})
        modifies this
        ensures this.k == old(this.k)
        ensures this.next == old(this.next)
        ensures this.prev == old(this.prev)
        ensures this.last == old(this.last)
        ensures this.len == old(this.len)
        ensures this.rlen == old(this.rlen)
        ensures this.keys == old(this.keys)
        ensures this.repr == repr
        ensures Br' == Br + {this, this.prev}
    {
        Br' := Br;
        this.repr := repr;
        Br' := Br' + {this};
        Br' := Br' + {this.prev};
    }

    ghost method AddToLastRepr(Br: set<CircularNode>, node: CircularNode)
        returns (Br': set<CircularNode>)
        requires this.last == this
        modifies this
        ensures this.k == old(this.k)
        ensures this.next == old(this.next)
        ensures this.prev == old(this.prev)
        ensures this.last == old(this.last)
        ensures this.len == old(this.len)
        ensures this.rlen == old(this.rlen)
        ensures this.keys == old(this.keys)
        ensures this.repr == old(this.repr) + {node}
        ensures Br' == Br + {this}
    {
        Br' := Br;
        this.repr := this.repr + {node};
        Br' := Br' + {this};
    }

    ghost method AddToLastKeys(Br: set<CircularNode>, k: int)
        returns (Br': set<CircularNode>)
        requires this.last == this
        modifies this
        ensures this.k == old(this.k)
        ensures this.next == old(this.next)
        ensures this.prev == old(this.prev)
        ensures this.last == old(this.last)
        ensures this.len == old(this.len)
        ensures this.rlen == old(this.rlen)
        ensures this.keys == old(this.keys) + {k}
        ensures this.repr == old(this.repr)
        ensures Br' == Br + {this}
    {
        Br' := Br;
        this.keys := this.keys + {k};
        Br' := Br' + {this};
    }

    ghost method DeleteFromLastRepr(Br: set<CircularNode>, node: CircularNode)
        returns (Br': set<CircularNode>)
        requires this.last == this && node.next == node && node.prev == node
        modifies this
        ensures this.k == old(this.k)
        ensures this.next == old(this.next)
        ensures this.prev == old(this.prev)
        ensures this.last == old(this.last)
        ensures this.len == old(this.len)
        ensures this.rlen == old(this.rlen)
        ensures this.keys == old(this.keys)
        ensures this.repr == old(this.repr) - {node}
        ensures Br' == Br + {this}
    {
        Br' := Br;
        this.repr := this.repr - {node};
        Br' := Br' + {this};
    }

    ghost method DeleteFromLastKeys(Br: set<CircularNode>, k: int)
        returns (Br': set<CircularNode>)
        requires this.last == this
        modifies this
        ensures this.k == old(this.k)
        ensures this.next == old(this.next)
        ensures this.prev == old(this.prev)
        ensures this.last == old(this.last)
        ensures this.len == old(this.len)
        ensures this.rlen == old(this.rlen)
        ensures this.keys == old(this.keys) - {k}
        ensures this.repr == old(this.repr)
        ensures Br' == Br + {this}
    {
        Br' := Br;
        this.keys := this.keys - {k};
        Br' := Br' + {this};
    }
}

lemma {:axiom} IfNotBr_ThenLC(Br: set<CircularNode>, x: CircularNode?)
    ensures x != null && x !in Br ==> x.LC()

ghost method AssertLCAndRemove(Br: set<CircularNode>, x: CircularNode?)
    returns (Br': set<CircularNode>)
    ensures (x != null && x.LC()) ==> Br' == Br - {x}
    ensures (x == null || !x.LC()) ==> Br' == Br
{
    if x != null && x.LC() {
        Br' := Br - {x};
    } else {
        Br' := Br;
    }
}
