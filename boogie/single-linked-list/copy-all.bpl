// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions"
// by Anonymous Authors.
// 
// Artifact by Anonymous Author, 2023. 
//
// Verification of single-linked list deep copy.

procedure SLLCopyAllContract(x: Ref) returns (ret: Ref);
    requires RefSetsEqual(Br, EmptyRefSet);
    requires x != null ==> LC(C.k, C.next, C.prev,
                                C.keys, C.repr, x);
    modifies Br, C.k, C.next, C.prev, C.keys, C.repr, alloc;
    ensures RefSetSubset(old(alloc), alloc);
    ensures ret == null <==> x == null;
    ensures ret != null ==> (
        LC(C.k, C.next, C.prev,
            C.keys, C.repr, ret)
        && KeySetsEqual(C.keys[ret], old(C.keys)[x])
        && Fresh(C.repr[ret], alloc, old(alloc))
        && (x != null ==> RefSetsDisjoint(C.repr[ret], C.repr[x]))
        && C.prev[ret] == null
    );
    ensures RefSetsEqual(Br, EmptyRefSet);
    // Framing conditions.
    ensures Frame_all(
        C.k, C.next, C.prev, 
        C.keys, C.repr,
        old(C.k), old(C.next), old(C.prev),
        old(C.keys), old(C.repr),
        EmptyRefSet, // the trick is that frame_all only considers those in the old alloc set.
        old(alloc)
    );

procedure SLLCopyAll(x: Ref) returns (ret: Ref)
    requires RefSetsEqual(Br, EmptyRefSet);
    requires x != null ==> LC(C.k, C.next, C.prev,
                                C.keys, C.repr, x);
    modifies Br, C.k, C.next, C.prev, C.keys, C.repr, alloc;
    ensures RefSetSubset(old(alloc), alloc);
    ensures ret == null <==> x == null;
    ensures ret != null ==> (
        LC(C.k, C.next, C.prev,
            C.keys, C.repr, ret)
        && KeySetsEqual(C.keys[ret], old(C.keys)[x])
        && Fresh(C.repr[ret], alloc, old(alloc))
        && (x != null ==> RefSetsDisjoint(C.repr[ret], C.repr[x]))
        && C.prev[ret] == null
    );
    ensures RefSetsEqual(Br, EmptyRefSet);
    // Framing conditions.
    ensures Frame_all(
        C.k, C.next, C.prev, 
        C.keys, C.repr,
        old(C.k), old(C.next), old(C.prev),
        old(C.keys), old(C.repr),
        EmptyRefSet, // the trick is that frame_all only considers those in the old alloc set.
        old(alloc)
    );
{
    // Local variables
    var newNode: Ref;
    var tmp: Ref;

    // Subexpressions
    var x_next: Ref; var x_k: int;
    var newNode_k: int;
    var newNode_next: Ref;
    var newNode_next_keys: KeySet; var newNode_next_repr: RefSet;

    call InAllocParam(x);

    if (x == null) {
        ret := x;
    } else {
        call x_next := Get_next(x);
        call IfNotBr_ThenLC(x_next);
        call tmp := SLLCopyAllContract(x_next);
        call x_k := Get_k(x);
        call newNode := Create(x_k);
        call Set_next(newNode, tmp);
        if (tmp != null) {
            call Set_prev(tmp, newNode);
        }
        
        call newNode_k := Get_k(newNode);
        call newNode_next := Get_next(newNode);
        if (newNode_next != null) {
            call newNode_next_keys := Get_keys(newNode_next);
            call newNode_next_repr := Get_repr(newNode_next);
        }
        call Set_keys(
            newNode, 
            (if newNode_next == null then EmptyKeySet else newNode_next_keys)[newNode_k := true]
        );
        call Set_repr(
            newNode, 
            (if newNode_next == null then EmptyRefSet else newNode_next_repr)[newNode := true]
        );
        call Set_prev(newNode, null);

        call AssertLCAndRemove(tmp);
        call AssertLCAndRemove(newNode);
        ret := newNode;
    }
}
