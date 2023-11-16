// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions of Datastructures"
// by Anonymous Authors.
// 
// Artifact by Anonymous Author, 2023. 
//
// Verification of Sorted List Reverse (iterative, destructive).

procedure SortedListReverse(x: Ref) returns (ret: Ref)
    requires RefSetsEqual(Br, EmptyRefSet);
    requires x != null ==> LC(C.k, C.next, C.prev, C.keys, C.repr, C.sorted, C.rev_sorted, x);
    requires x != null ==> C.sorted[x] && C.prev[x] == null;
    modifies Br, C.k, C.next, C.prev, 
            C.keys, C.repr, C.sorted, C.rev_sorted;
    ensures ret == null <==> x == null;
    ensures ret != null ==> (
        LC(C.k, C.next, C.prev, 
            C.keys, C.repr, C.sorted, C.rev_sorted, 
            ret)
        && C.rev_sorted[ret]
        && KeySetsEqual(C.keys[ret], old(C.keys)[x])
        && RefSetsEqual(C.repr[ret], old(C.repr)[x])
        && C.prev[ret] == null
    );
    ensures RefSetsEqual(Br, EmptyRefSet);
    // Framing conditions.
    ensures Frame_all(
        C.k, C.next, C.prev, 
        C.keys, C.repr, C.sorted, C.rev_sorted,
        old(C.k), old(C.next), old(C.prev),
        old(C.keys), old(C.repr), old(C.sorted), old(C.rev_sorted),
        if x == null then EmptyRefSet else old(C.repr)[x], old(alloc)
    );
{
    // Local variables
    var oldList: Ref;
    var tmp: Ref;

    // Subexpressions
    var oldList_next: Ref; var oldList_k: int;
    var oldList_next_keys: KeySet; var oldList_next_repr: RefSet;
    
    call InAllocParam(x);

    oldList := x;
    ret := null;

    while (oldList != null)
        invariant oldList != null ==>
                        LC(C.k, C.next, C.prev, 
                            C.keys, C.repr, C.sorted, C.rev_sorted, 
                            oldList)
                        && C.sorted[oldList]
                        && C.prev[oldList] == null;
        invariant ret != null ==>
                        LC(C.k, C.next, C.prev, 
                            C.keys, C.repr, C.sorted, C.rev_sorted, 
                            ret)
                        && C.rev_sorted[ret]
                        && C.prev[ret] == null;
        invariant oldList != null && ret != null ==>
                        C.k[ret] <= C.k[oldList];
        invariant x != null ==> (
            KeySetsEqual(
                old(C.keys)[x],
                KeySetUnionF(
                    if oldList == null then EmptyKeySet else C.keys[oldList],
                    if ret == null then EmptyKeySet else C.keys[ret]
                )
            )
            && RefSetsEqual(
                    old(C.repr)[x],
                    RefSetUnionF(
                        if oldList == null then EmptyRefSet else C.repr[oldList],
                        if ret == null then EmptyRefSet else C.repr[ret]
                    )
                )
        );
        invariant RefSetsDisjoint(
            if oldList == null then EmptyRefSet else C.repr[oldList],
            if ret == null then EmptyRefSet else C.repr[ret]
        );
        invariant x == null ==> ret == null;
        invariant RefSetsEqual(Br, EmptyRefSet);
        // Additional invariant required when not proving termination
        invariant RefSetSubset(
            if oldList == null then EmptyRefSet else C.repr[oldList],
            if x == null then EmptyRefSet else old(C.repr)[x]
        );
        invariant Frame_all(
            C.k, C.next, C.prev, 
            C.keys, C.repr, C.sorted, C.rev_sorted,
            old(C.k), old(C.next), old(C.prev),
            old(C.keys), old(C.repr), old(C.sorted), old(C.rev_sorted),
            if x == null then EmptyRefSet else old(C.repr)[x], old(alloc)
        );
    {
        call tmp := Get_next(oldList);
        if (tmp != null) {
            call IfNotBr_ThenLC(tmp);
            call Set_prev(tmp, null);
        }
        call Set_next(oldList, ret);
        if (ret != null) {
            call Set_prev(ret, oldList);
        }
        call oldList_k := Get_k(oldList);
        call oldList_next := Get_next(oldList);
        if (oldList_next != null) {
            call oldList_next_keys := Get_keys(oldList_next);
            call oldList_next_repr := Get_repr(oldList_next);
        }
        call Set_keys(
            oldList, 
            (if oldList_next == null then EmptyKeySet else oldList_next_keys)[oldList_k := true]
        );
        call Set_repr(
            oldList, 
            (if oldList_next == null then EmptyRefSet else oldList_next_repr)[oldList := true]
        );
        call Set_sorted(oldList, false);
        call Set_rev_sorted(oldList, true);
        call AssertLCAndRemove(oldList);
        call AssertLCAndRemove(ret);
        call AssertLCAndRemove(tmp);
        ret := oldList;
        oldList := tmp;
    }
}
