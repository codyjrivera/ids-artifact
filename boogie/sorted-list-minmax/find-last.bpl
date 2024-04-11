// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions"
// by Adithya Murali, Cody Rivera, and P. Madhusudan.
// 
// Artifact by Cody Rivera, 2023-2024. 
//
// Verification of Sorted List Find Last (with min/max maps).
    
procedure SortedListFindLast(x: Ref) returns (ret: Ref)
    requires x != null;
    requires RefSetsEqual(Br, EmptyRefSet);
    requires LC(C.k, C.next, C.prev, 
                C.keys, C.repr, C.sorted, C.rev_sorted, 
                C.min, C.max, x);
    requires C.sorted[x];
    ensures ret != null;
    ensures LC(C.k, C.next, C.prev, 
                C.keys, C.repr, C.sorted, C.rev_sorted, 
                C.min, C.max, ret);
    ensures C.next[ret] == null;
    ensures (C.repr[x])[ret] && (C.keys[x])[C.k[x]];
    ensures C.k[ret] == C.max[x];
    ensures RefSetsEqual(Br, EmptyRefSet);
{
    var cur: Ref;
    var cur_next: Ref;

    call InAllocParam(x);

    cur := x;
    call cur_next := Get_next(x);

    while (cur_next != null) 
        invariant cur != null;
        invariant cur_next == C.next[cur];
        invariant LC(C.k, C.next, C.prev, 
                C.keys, C.repr, C.sorted, C.rev_sorted, 
                C.min, C.max, cur);
        invariant C.sorted[cur];
        invariant RefSetSubset(C.repr[cur], C.repr[x]);
        invariant KeySetSubset(C.keys[cur], C.keys[x]);
        invariant C.max[cur] == C.max[x];
    {
        call IfNotBr_ThenLC(cur_next);
        cur := cur_next;
        call cur_next := Get_next(cur);
    }

    ret := cur;
}
