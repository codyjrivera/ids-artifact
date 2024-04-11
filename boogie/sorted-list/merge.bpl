// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions"
// by Adithya Murali, Cody Rivera, and P. Madhusudan.
// 
// Artifact by Cody Rivera, 2023-2024. 
//
// Verification of Sorted List Merge (destructive).

procedure SortedListMergeContract(x1: Ref, x2: Ref) returns (ret: Ref);
    requires RefSetsDisjoint(
        Br, 
        RefSetUnionF(
            if x1 == null then EmptyRefSet else C.repr[x1],
            if x2 == null then EmptyRefSet else C.repr[x2]
        )
    );
    requires x1 != null ==> (
        LC(C.k, C.next, C.prev, 
            C.keys, C.repr, C.sorted, C.rev_sorted, 
            x1)
        && C.sorted[x1] && C.prev[x1] == null  
    );
    requires x2 != null ==> (
        LC(C.k, C.next, C.prev, 
            C.keys, C.repr, C.sorted, C.rev_sorted, 
            x2)
        && C.sorted[x2] && C.prev[x2] == null  
    );
    requires RefSetsDisjoint(
        if x1 == null then EmptyRefSet else C.repr[x1],
        if x2 == null then EmptyRefSet else C.repr[x2]
    );
    modifies Br, C.k, C.next, C.prev, 
            C.keys, C.repr, C.sorted, C.rev_sorted;
    ensures ret == null <==> x1 == null && x2 == null;
    ensures ret != null ==> (
        LC(C.k, C.next, C.prev, 
            C.keys, C.repr, C.sorted, C.rev_sorted, 
            ret)
        && C.sorted[ret]
        && (x1 == null ==> C.k[ret] == old(C.k)[x2])
        && (x2 == null ==> C.k[ret] == old(C.k)[x1])
        && (x1 != null && x2 != null ==>
                C.k[ret] == if old(C.k)[x1] <= old(C.k)[x2] then
                                old(C.k)[x1]
                            else
                                old(C.k)[x2])
        && C.prev[ret] == null
        && KeySetsEqual(
                C.keys[ret],
                KeySetUnionF(
                    if x1 == null then EmptyKeySet else old(C.keys)[x1],
                    if x2 == null then EmptyKeySet else old(C.keys)[x2]
                )
            )
        && RefSetsEqual(
                C.repr[ret],
                RefSetUnionF(
                    if x1 == null then EmptyRefSet else old(C.repr)[x1],
                    if x2 == null then EmptyRefSet else old(C.repr)[x2]
                )
            )
    );
    ensures RefSetsEqual(Br, old(Br));
    // Framing conditions.
    ensures Frame_all(
        C.k, C.next, C.prev, 
        C.keys, C.repr, C.sorted, C.rev_sorted,
        old(C.k), old(C.next), old(C.prev),
        old(C.keys), old(C.repr), old(C.sorted), old(C.rev_sorted),
        RefSetUnionF(
            if x1 == null then EmptyRefSet else old(C.repr)[x1],
            if x2 == null then EmptyRefSet else old(C.repr)[x2]
        ), 
        old(alloc)
    );

procedure SortedListMerge(x1: Ref, x2: Ref) returns (ret: Ref)
    requires RefSetsDisjoint(
        Br, 
        RefSetUnionF(
            if x1 == null then EmptyRefSet else C.repr[x1],
            if x2 == null then EmptyRefSet else C.repr[x2]
        )
    );
    requires x1 != null ==> (
        LC(C.k, C.next, C.prev, 
            C.keys, C.repr, C.sorted, C.rev_sorted, 
            x1)
        && C.sorted[x1] && C.prev[x1] == null  
    );
    requires x2 != null ==> (
        LC(C.k, C.next, C.prev, 
            C.keys, C.repr, C.sorted, C.rev_sorted, 
            x2)
        && C.sorted[x2] && C.prev[x2] == null  
    );
    requires RefSetsDisjoint(
        if x1 == null then EmptyRefSet else C.repr[x1],
        if x2 == null then EmptyRefSet else C.repr[x2]
    );
    modifies Br, C.k, C.next, C.prev, 
            C.keys, C.repr, C.sorted, C.rev_sorted;
    ensures ret == null <==> x1 == null && x2 == null;
    ensures ret != null ==> (
        LC(C.k, C.next, C.prev, 
            C.keys, C.repr, C.sorted, C.rev_sorted, 
            ret)
        && C.sorted[ret]
        && (x1 == null ==> C.k[ret] == old(C.k)[x2])
        && (x2 == null ==> C.k[ret] == old(C.k)[x1])
        && (x1 != null && x2 != null ==>
                C.k[ret] == if old(C.k)[x1] <= old(C.k)[x2] then
                                old(C.k)[x1]
                            else
                                old(C.k)[x2])
        && C.prev[ret] == null
        && KeySetsEqual(
                C.keys[ret],
                KeySetUnionF(
                    if x1 == null then EmptyKeySet else old(C.keys)[x1],
                    if x2 == null then EmptyKeySet else old(C.keys)[x2]
                )
            )
        && RefSetsEqual(
                C.repr[ret],
                RefSetUnionF(
                    if x1 == null then EmptyRefSet else old(C.repr)[x1],
                    if x2 == null then EmptyRefSet else old(C.repr)[x2]
                )
            )
    );
    ensures RefSetsEqual(Br, old(Br));
    // Framing conditions.
    ensures Frame_all(
        C.k, C.next, C.prev, 
        C.keys, C.repr, C.sorted, C.rev_sorted,
        old(C.k), old(C.next), old(C.prev),
        old(C.keys), old(C.repr), old(C.sorted), old(C.rev_sorted),
        RefSetUnionF(
            if x1 == null then EmptyRefSet else old(C.repr)[x1],
            if x2 == null then EmptyRefSet else old(C.repr)[x2]
        ), 
        old(alloc)
    );
{
    // Local variables
    var x1n: Ref;
    var x2n: Ref;
    var tl: Ref;

    // Subexpressions
    var x1_k: int; var x2_k: int;
    var x1_next: Ref;
    var x1_next_keys: KeySet; var x1_next_repr: RefSet;
    var x2_next: Ref;
    var x2_next_keys: KeySet; var x2_next_repr: RefSet;

    call InAllocParam(x1);
    call InAllocParam(x2);

    if (x1 == null) {
        ret := x2;
    } else if (x2 == null) {
        ret := x1;
    } else {
        call x1_k := Get_k(x1);
        call x2_k := Get_k(x2);

        if (x1_k <= x2_k) {
            call x1n := Get_next(x1);
            call IfNotBr_ThenLC(x1n);

            call Set_next(x1, null);
            if (x1n != null) {
                call Set_prev(x1n, null);
            }
            call AssertLCAndRemove(x1n);

            call tl := SortedListMergeContract(x1n, x2);
            call Set_next(x1, tl);
            
            call x1_k := Get_k(x1);
            call x1_next := Get_next(x1);
            if (x1_next != null) {
                call x1_next_keys := Get_keys(x1_next);
                call x1_next_repr := Get_repr(x1_next);
            }
            call Set_keys(
                x1, 
                (if x1_next == null then EmptyKeySet else x1_next_keys)[x1_k := true]
            );
            call Set_repr(
                x1, 
                (if x1_next == null then EmptyRefSet else x1_next_repr)[x1 := true]
            );

            if (tl != null) {
                call Set_prev(tl, x1);
            }

            call AssertLCAndRemove(x1);
            call AssertLCAndRemove(tl);

            ret := x1;
        } else {
            call x2n := Get_next(x2);
            call IfNotBr_ThenLC(x2n);

            call Set_next(x2, null);
            if (x2n != null) {
                call Set_prev(x2n, null);
            }
            call AssertLCAndRemove(x2n);

            call tl := SortedListMergeContract(x1, x2n);
            call Set_next(x2, tl);
            
            call x2_k := Get_k(x2);
            call x2_next := Get_next(x2);
            if (x2_next != null) {
                call x2_next_keys := Get_keys(x2_next);
                call x2_next_repr := Get_repr(x2_next);
            }
            call Set_keys(
                x2, 
                (if x2_next == null then EmptyKeySet else x2_next_keys)[x2_k := true]
            );
            call Set_repr(
                x2, 
                (if x2_next == null then EmptyRefSet else x2_next_repr)[x2 := true]
            );

            if (tl != null) {
                call Set_prev(tl, x2);
            }

            call AssertLCAndRemove(x2);
            call AssertLCAndRemove(tl);

            ret := x2;
        }
    }
}