// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions"
// by Anonymous Authors.
// 
// Artifact by Anonymous Author, 2023. 
//
// Verification of Singly Linked List Delete All.

procedure SLLDeleteAllContract(x: Ref, k: int) returns (ret: Ref);
    requires RefSetsDisjoint(Br, if x == null then EmptyRefSet else C.repr[x]);
    requires x != null ==> LC(C.k, C.next, C.prev, C.keys, C.repr, x);
    requires x != null ==> C.prev[x] == null;
    modifies Br, C.k, C.next, C.prev, 
            C.keys, C.repr;
    ensures x == null || KeySetsEqual(old(C.keys)[x], EmptyKeySet[k := true]) ==> ret == null;
    ensures (x != null && !KeySetsEqual(old(C.keys)[x], EmptyKeySet) 
                && !KeySetsEqual(old(C.keys)[x], EmptyKeySet[k := true]))
                ==> ret != null;
    ensures ret != null ==> (
        LC(C.k, C.next, C.prev, 
            C.keys, C.repr, 
            ret)
        && KeySetsEqual(C.keys[ret], (old(C.keys)[x])[k := false])
        && RefSetSubset(C.repr[ret], old(C.repr)[x])
        && C.prev[ret] == null
    );
    ensures RefSetsEqual(Br, old(Br));
    // Framing conditions.
    ensures Frame_all(
        C.k, C.next, C.prev, 
        C.keys, C.repr,
        old(C.k), old(C.next), old(C.prev),
        old(C.keys), old(C.repr),
        if x == null then EmptyRefSet else old(C.repr)[x], old(alloc)
    );

procedure SLLDeleteAll(x: Ref, k: int) returns (ret: Ref)
    requires RefSetsDisjoint(Br, if x == null then EmptyRefSet else C.repr[x]);
    requires x != null ==> LC(C.k, C.next, C.prev, C.keys, C.repr, x);
    requires x != null ==> C.prev[x] == null;
    modifies Br, C.k, C.next, C.prev, 
            C.keys, C.repr;
    ensures x == null || KeySetsEqual(old(C.keys)[x], EmptyKeySet[k := true]) ==> ret == null;
    ensures (x != null && !KeySetsEqual(old(C.keys)[x], EmptyKeySet) 
                && !KeySetsEqual(old(C.keys)[x], EmptyKeySet[k := true]))
                ==> ret != null;
    ensures ret != null ==> (
        LC(C.k, C.next, C.prev, 
            C.keys, C.repr, 
            ret)
        && KeySetsEqual(C.keys[ret], (old(C.keys)[x])[k := false])
        && RefSetSubset(C.repr[ret], old(C.repr)[x])
        && C.prev[ret] == null
    );
    ensures RefSetsEqual(Br, old(Br));
    // Framing conditions.
    ensures Frame_all(
        C.k, C.next, C.prev, 
        C.keys, C.repr,
        old(C.k), old(C.next), old(C.prev),
        old(C.keys), old(C.repr),
        if x == null then EmptyRefSet else old(C.repr)[x], old(alloc)
    );
{
    // Local variables
    var xn: Ref;
    var tmp: Ref;

    // Subexpressions
    var x_k: int; var x_next: Ref; 
    var x_next_keys: KeySet; var x_next_repr: RefSet;

    call InAllocParam(x);

    if (x != null) {
        call x_k := Get_k(x);
    }
    if (x == null) {
        ret := x;
    } else if (x_k == k) {
        call xn := Get_next(x);
        call IfNotBr_ThenLC(xn);
        call Set_next(x, null);
        if (xn != null) {
            call Set_prev(xn, null);
        }
        call AssertLCAndRemove(xn);
        call Set_keys(x, EmptyKeySet[x_k := true]);
        call Set_repr(x, EmptyRefSet[x := true]);
        call AssertLCAndRemove(x);

        call tmp := SLLDeleteAllContract(xn, k);
        ret := tmp;
    } else {
        call xn := Get_next(x);
        call IfNotBr_ThenLC(xn);
        call Set_next(x, null);
        if (xn != null) {
            call Set_prev(xn, null);
        }
        call AssertLCAndRemove(xn);

        call tmp := SLLDeleteAllContract(xn, k);
        call Set_next(x, tmp);
        if (tmp != null) {
            call Set_prev(tmp, x);
        }

        call x_k := Get_k(x);
        call x_next := Get_next(x);
        if (x_next != null) {
            call x_next_keys := Get_keys(x_next);
            call x_next_repr := Get_repr(x_next);
        }
        call Set_keys(
            x, 
            (if x_next == null then EmptyKeySet else x_next_keys)[x_k := true]
        );
        call Set_repr(
            x, 
            (if x_next == null then EmptyRefSet else x_next_repr)[x := true]
        );

        call AssertLCAndRemove(x);
        call AssertLCAndRemove(tmp);
        ret := x;
    }
}