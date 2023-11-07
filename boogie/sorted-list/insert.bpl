// Supporting Artifact for
// "Predictive Verification using Intrinsic Definitions of Data Structures"
// by Adithya Murali, Cody Rivera, and P. Madhusudan.
// 
// Artifact by Cody Rivera, 2023. 
//
// Verification of Sorted List Insert.

procedure SortedListInsertContract(x: Ref, k: int) returns (ret: Ref);
    requires RefSetsEqual(Br, EmptyRefSet);
    requires LC(C.k, C.next, C.prev, C.keys, C.repr, C.sorted, C.rev_sorted, x, alloc);
    requires x != null ==> C.sorted[x];
    modifies Br, alloc, C.k, C.next, C.prev, C.keys, C.repr, C.sorted, C.rev_sorted;
    ensures RefSetSubset(old(alloc), alloc);
    ensures ret != null;
    ensures LC(C.k, C.next, C.prev, C.keys, C.repr, C.sorted, C.rev_sorted, ret, alloc);
    ensures C.sorted[ret];
    ensures C.k[ret] == (if x != null && old(C.k)[x] <= k then old(C.k)[x] else k);
    ensures KeySetsEqual(C.keys[ret], (if x == null then EmptyKeySet else old(C.keys)[x])[k := true]);
    ensures Fresh(RefSetDiffF(C.repr[ret], (if x == null then EmptyRefSet else old(C.repr)[x])), alloc, old(alloc));
    ensures C.prev[ret] == null;
    ensures x != null ==> (ret == x || C.next[ret] == x);
    ensures (x == null || old(C.prev)[x] == null) ==> RefSetsEqual(Br, EmptyRefSet);
    ensures (x != null && old(C.prev)[x] != null) ==> RefSetsEqual(Br, EmptyRefSet[old(C.prev)[x] := true]);
    // Framing conditions.
    ensures Frame_all(C.k, C.next, C.prev, C.keys, C.repr, C.sorted, C.rev_sorted,
                      old(C.k), old(C.next), old(C.prev), old(C.keys), old(C.repr), old(C.sorted), old(C.rev_sorted),
                      if x == null then EmptyRefSet else old(C.repr)[x], old(alloc));

procedure SortedListInsert(x: Ref, k: int) returns (ret: Ref)
    requires RefSetsEqual(Br, EmptyRefSet);
    requires LC(C.k, C.next, C.prev, C.keys, C.repr, C.sorted, C.rev_sorted, x, alloc);
    requires x != null ==> C.sorted[x];
    modifies Br, alloc, C.k, C.next, C.prev, C.keys, C.repr, C.sorted, C.rev_sorted;
    ensures RefSetSubset(old(alloc), alloc);
    ensures ret != null;
    ensures LC(C.k, C.next, C.prev, C.keys, C.repr, C.sorted, C.rev_sorted, ret, alloc);
    ensures C.sorted[ret];
    ensures C.k[ret] == (if x != null && old(C.k)[x] <= k then old(C.k)[x] else k);
    ensures KeySetsEqual(C.keys[ret], (if x == null then EmptyKeySet else old(C.keys)[x])[k := true]);
    ensures Fresh(RefSetDiffF(C.repr[ret], (if x == null then EmptyRefSet else old(C.repr)[x])), alloc, old(alloc));
    ensures C.prev[ret] == null;
    ensures x != null ==> (ret == x || C.next[ret] == x);
    ensures (x == null || old(C.prev)[x] == null) ==> RefSetsEqual(Br, EmptyRefSet);
    ensures (x != null && old(C.prev)[x] != null) ==> RefSetsEqual(Br, EmptyRefSet[old(C.prev)[x] := true]);
    // Framing conditions.
    ensures Frame_all(C.k, C.next, C.prev, C.keys, C.repr, C.sorted, C.rev_sorted,
                      old(C.k), old(C.next), old(C.prev), old(C.keys), old(C.repr), old(C.sorted), old(C.rev_sorted),
                      if x == null then EmptyRefSet else old(C.repr)[x], old(alloc));
{
    // Local variables
    var node: Ref;
    var tmp: Ref;
    var oldnext: Ref;

    if (x == null) {
        call node := Create(k);
        call Set_keys(node, EmptyKeySet[k := true]);
        call Set_repr(node, EmptyRefSet[node := true]);
        call Set_sorted(node, true);
        call Set_rev_sorted(node, false);

        call AssertLCAndRemove(node);

        ret := node;
    } else if (k <= C.k[x]) {
        call node := Create(k);
        call Set_next(node, x);
        call Set_prev(node, null);
        call Set_keys(node, (if C.next[node] == null then EmptyKeySet else C.keys[C.next[node]])[C.k[node] := true]);
        call Set_repr(node, (if C.next[node] == null then EmptyRefSet else C.repr[C.next[node]])[node := true]);
        call Set_sorted(node, true);
        call Set_rev_sorted(node, false);
        call Set_prev(x, node);

        call AssertLCAndRemove(x);
        call AssertLCAndRemove(node);

        ret := node;
    } else {
        if (C.next[x] != null) {
            call IfNotBr_ThenLC(C.next[x]);
        }

        call tmp := SortedListInsertContract(C.next[x], k);

        if (C.next[x] != null) {
            call IfNotBr_ThenLC(C.next[x]);
        }

        oldnext := C.next[x];
        call Set_prev(tmp, x);
        call Set_next(x, tmp);
        call AssertLCAndRemove(tmp);
        call AssertLCAndRemove(oldnext);

        call Set_keys(x, (if C.next[x] == null then EmptyKeySet else C.keys[C.next[x]])[C.k[x] := true]);
        call Set_repr(x, (if C.next[x] == null then EmptyRefSet else C.repr[C.next[x]])[x := true]);
        call Set_prev(x, null);

        call AssertLCAndRemove(x);
        ret := x;
    }
}
