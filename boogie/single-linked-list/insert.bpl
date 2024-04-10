// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions"
// by Anonymous Authors.
// 
// Artifact by Anonymous Author, 2023. 
//
// Verification of Single Linked List Insert (as if it were sorted).

// NOTE: We know that we can soundly apply the fix-what-you-break
// (FWYB) framework if a given program is well-behaved. To ensure this,
// we construct programs such that the only way that they mutate the heap,
// assign to the broken set Br, or allocate memory is through a set of
// carefully-designed macros shown below. It is easy to see that the
// body of the procedure SLLInsert meets this condition.
//
// Here are the macros used in this file, which appear in Section 4.1:
// - Create (defined in single-linked-list.bpl, Line 103)
// - Set_{field} (defined in single-linked-list.bpl, Lines 113-156)
// - IfNotBr_ThenLC (defined in single-linked-list.bpl, Line 160)
// - AssertLCAndRemove (defined in single-linked-list.bpl, Line 164)
//
// We also use the macro InAllocParam, which asserts that an object,
// and all of the objects it refers to, are allocated. We can use this
// macro soundly since we model a garbage collected language, and any
// object we can access must be allocated. The macro appears in 
// single-linked-list.bpl, Line 221.
//
// We additionally associate each Set_{field} macro with its impact
// set proof Check_Set_{field}, ensuring that the broken set is updated
// correctly. The Set_{field} macros are in single-linked-list.bpl, while
// the Check_Set_{field} proofs are in impact-sets.bpl.

procedure SLLInsertContract(x: Ref, k: int) returns (ret: Ref);
    requires RefSetsEqual(Br, EmptyRefSet);
    requires LC(C.k, C.next, C.prev, C.keys, C.repr, x);
    modifies Br, alloc, C.k, C.next, C.prev, C.keys, C.repr;
    ensures RefSetSubset(old(alloc), alloc);
    ensures ret != null;
    ensures LC(C.k, C.next, C.prev, C.keys, C.repr, ret);
    ensures KeySetsEqual(C.keys[ret], (if x == null then EmptyKeySet else old(C.keys)[x])[k := true]);
    ensures Fresh(RefSetDiffF(C.repr[ret], (if x == null then EmptyRefSet else old(C.repr)[x])), alloc, old(alloc));
    ensures C.prev[ret] == null;
    ensures x != null ==> (ret == x || C.next[ret] == x);
    ensures (x == null || old(C.prev)[x] == null) ==> RefSetsEqual(Br, EmptyRefSet);
    ensures (x != null && old(C.prev)[x] != null) ==> RefSetsEqual(Br, EmptyRefSet[old(C.prev)[x] := true]);
    // Framing conditions.
    ensures Frame_all(C.k, C.next, C.prev, C.keys, C.repr,
                      old(C.k), old(C.next), old(C.prev), old(C.keys), old(C.repr),
                      if x == null then EmptyRefSet else old(C.repr)[x], old(alloc));

procedure SLLInsert(x: Ref, k: int) returns (ret: Ref)
    requires RefSetsEqual(Br, EmptyRefSet);
    requires LC(C.k, C.next, C.prev, C.keys, C.repr, x);
    modifies Br, alloc, C.k, C.next, C.prev, C.keys, C.repr;
    ensures RefSetSubset(old(alloc), alloc);
    ensures ret != null;
    ensures LC(C.k, C.next, C.prev, C.keys, C.repr, ret);
    ensures KeySetsEqual(C.keys[ret], (if x == null then EmptyKeySet else old(C.keys)[x])[k := true]);
    ensures Fresh(RefSetDiffF(C.repr[ret], (if x == null then EmptyRefSet else old(C.repr)[x])), alloc, old(alloc));
    ensures C.prev[ret] == null;
    ensures x != null ==> (ret == x || C.next[ret] == x);
    ensures (x == null || old(C.prev)[x] == null) ==> RefSetsEqual(Br, EmptyRefSet);
    ensures (x != null && old(C.prev)[x] != null) ==> RefSetsEqual(Br, EmptyRefSet[old(C.prev)[x] := true]);
    // Framing conditions.
    ensures Frame_all(C.k, C.next, C.prev, C.keys, C.repr,
                      old(C.k), old(C.next), old(C.prev), old(C.keys), old(C.repr),
                      if x == null then EmptyRefSet else old(C.repr)[x], old(alloc));
{
    // Local variables
    var node: Ref;
    var tmp: Ref;
    var oldnext: Ref;

    // Subexpressions
    var node_next: Ref;
    var node_next_keys: KeySet;
    var node_next_repr: RefSet;
    var node_k: int;
    var x_next: Ref;
    var x_next_keys: KeySet;
    var x_next_repr: RefSet;
    var x_k: int;

    call InAllocParam(x);
    if (x == null) {
        call node := Create(k);
        call Set_keys(node, EmptyKeySet[k := true]);
        call Set_repr(node, EmptyRefSet[node := true]);

        call AssertLCAndRemove(node);

        ret := node;
    } else if (k <= C.k[x]) {
        call node := Create(k);
        call Set_next(node, x);
        call Set_prev(node, null);
        call node_next := Get_next(node);
        call node_k := Get_k(node);
        if (node_next != null) {
            call node_next_keys := Get_keys(node_next);
            call node_next_repr := Get_repr(node_next);
        }
        call Set_keys(node, (if node_next == null then EmptyKeySet else node_next_keys)[node_k := true]);
        call Set_repr(node, (if node_next == null then EmptyRefSet else node_next_repr)[node := true]);
        call Set_prev(x, node);

        call AssertLCAndRemove(x);
        call AssertLCAndRemove(node);

        ret := node;
    } else {
        call x_next := Get_next(x);

        call IfNotBr_ThenLC(x_next);
        call tmp := SLLInsertContract(x_next, k);

        call x_next := Get_next(x);
        call IfNotBr_ThenLC(x_next);

        oldnext := x_next;
        call Set_prev(tmp, x);
        call Set_next(x, tmp);
        call AssertLCAndRemove(tmp);
        call AssertLCAndRemove(oldnext);

        call x_next := Get_next(x);
        call x_k := Get_k(x);
        if (x_next != null) {
            call x_next_keys := Get_keys(x_next);
            call x_next_repr := Get_repr(x_next);
        }
        call Set_keys(x, (if x_next == null then EmptyKeySet else x_next_keys)[x_k := true]);
        call Set_repr(x, (if x_next == null then EmptyRefSet else x_next_repr)[x := true]);
        call Set_prev(x, null);

        call AssertLCAndRemove(x);
        ret := x;
    }
}