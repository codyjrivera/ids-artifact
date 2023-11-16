// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions of Datastructures"
// by Anonymous Authors.
// 
// Artifact by Anonymous Author, 2023. 
//
// Verification of Treap Find.

procedure TreapFindContract(x: Ref, k: int) returns (ret: Ref);
    requires RefSetsEqual(Br, EmptyRefSet);
    requires x != null ==> LC(C.k, C.prio, C.l, C.r, C.p, 
                                C.min, C.max, C.keys, C.repr,
                                x);
    ensures (ret != null ==>
                LC(C.k, C.prio, C.l, C.r, C.p, 
                    C.min, C.max, C.keys, C.repr,
                    x)
                && C.k[ret] == k
                && x != null
                && (C.keys[x])[k]);

procedure TreapFind(x: Ref, k: int) returns (ret: Ref)
    requires RefSetsEqual(Br, EmptyRefSet);
    requires x != null ==> LC(C.k, C.prio, C.l, C.r, C.p, 
                                C.min, C.max, C.keys, C.repr,
                                x);
    ensures (ret != null ==>
                LC(C.k, C.prio, C.l, C.r, C.p,
                    C.min, C.max, C.keys, C.repr,
                    x)
                && C.k[ret] == k
                && x != null
                && (C.keys[x])[k]);
{
    var x_k: int; var x_l: Ref; var x_r: Ref;

    call InAllocParam(x);

    if (x != null) {
        call x_k := Get_k(x);
        call x_l := Get_l(x);
        call x_r := Get_r(x);
    }
    if (x == null || k == x_k) {
        ret := x;
    } else if (k < x_k) {
        call IfNotBr_ThenLC(x_l);
        call IfNotBr_ThenLC(x_r);

        call ret := TreapFindContract(x_l, k);
    } else {
        call IfNotBr_ThenLC(x_l);
        call IfNotBr_ThenLC(x_r);

        call ret := TreapFindContract(x_r, k);
    }
}
