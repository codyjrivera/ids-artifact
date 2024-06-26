// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions"
// by Adithya Murali, Cody Rivera, and P. Madhusudan.
// 
// Artifact by Cody Rivera, 2023. 
//
// Verification of AVL Find Min.

procedure AVLFindMin(x: Ref) returns (ret: int)
    requires x != null;
    requires RefSetsDisjoint(Br, C.repr[x]);
    requires LC(C.k, C.l, C.r, C.p, C.height, 
                C.min, C.max, C.keys, C.repr,
                x);
    ensures (C.keys[x])[ret];
    ensures ret == C.min[x];
{
    var cur: Ref;
    var cur_l: Ref;

    call InAllocParam(x);

    cur := x;
    call cur_l := Get_l(cur);

    while (cur_l != null)
        invariant cur_l == C.l[cur];
        invariant cur != null;
        invariant LC(C.k, C.l, C.r, C.p, C.height, 
                C.min, C.max, C.keys, C.repr, 
                cur);
        invariant KeySetSubset(C.keys[cur], C.keys[x]);
        invariant RefSetSubset(C.repr[cur], C.repr[x]);
        invariant C.min[cur] == C.min[x];
    {
        call IfNotBr_ThenLC(cur_l);
        cur := cur_l;
        call cur_l := Get_l(cur);
    }

    call ret := Get_k(cur);
}
