// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions of Datastructures"
// by Anonymous Authors.
// 
// Artifact by Anonymous Author, 2023. 
//
// Verification of BST Insert.

procedure BSTInsertContract(x: Ref, k: int)
    returns (ret: Ref);
    requires Br == EmptyRefSet;
    requires x != null ==> LC(C.k, C.l, C.r, C.p, 
                                C.min, C.max, C.keys, C.repr,
                                x);
    requires x != null ==> !(C.keys[x])[k];
    modifies C.k, C.l, C.r, C.p,
        C.min, C.max, C.keys,
        C.repr, Br, alloc;
    ensures RefSetSubset(old(alloc), alloc);
    ensures ret != null;
    ensures LC(C.k, C.l, C.r, C.p, 
                C.min, C.max, C.keys, C.repr,
                ret);
    ensures C.p[ret] == null;
    ensures x != null ==> ret == x;
    ensures (x == null ==>
                KeySetsEqual(C.keys[ret], EmptyKeySet[k := true])
                && C.min[ret] == k
                && C.max[ret] == k
                && Fresh(C.repr[ret], alloc, old(alloc))
                && RefSetsEqual(Br, EmptyRefSet));
    ensures (x != null ==>
                KeySetsEqual(C.keys[ret], (old(C.keys)[x])[k := true])
                && (C.min[ret] == old(C.min)[x] || C.min[ret] == k)
                && (C.max[ret] == old(C.max)[x] || C.max[ret] == k)
                && Fresh(RefSetDiffF(C.repr[ret], old(C.repr)[x]), alloc, old(alloc))
                && (old(C.p)[x] == null ==> RefSetsEqual(Br, EmptyRefSet))
                && (old(C.p)[x] != null ==> RefSetsEqual(Br, EmptyRefSet[old(C.p)[x] := true])));
    // Framing conditions.
    ensures Frame_all(
        C.k, C.l, C.r, C.p,
        C.min, C.max, C.keys, C.repr,
        old(C.k), old(C.l), old(C.r), old(C.p), 
        old(C.min), old(C.max), old(C.keys), old(C.repr),
        if x == null then EmptyRefSet else old(C.repr)[x], old(alloc)
    );

procedure BSTInsert(x: Ref, k: int)
    returns (ret: Ref)
    requires Br == EmptyRefSet;
    requires x != null ==> LC(C.k, C.l, C.r, C.p, 
                                C.min, C.max, C.keys, C.repr,
                                x);
    requires x != null ==> !(C.keys[x])[k];
    modifies C.k, C.l, C.r, C.p,
        C.min, C.max, C.keys,
        C.repr, Br, alloc;
    ensures RefSetSubset(old(alloc), alloc);
    ensures ret != null;
    ensures LC(C.k, C.l, C.r, C.p, 
                C.min, C.max, C.keys, C.repr,
                ret);
    ensures C.p[ret] == null;
    ensures x != null ==> ret == x;
    ensures (x == null ==>
                KeySetsEqual(C.keys[ret], EmptyKeySet[k := true])
                && C.min[ret] == k
                && C.max[ret] == k
                && Fresh(C.repr[ret], alloc, old(alloc))
                && RefSetsEqual(Br, EmptyRefSet));
    ensures (x != null ==>
                KeySetsEqual(C.keys[ret], (old(C.keys)[x])[k := true])
                && (C.min[ret] == old(C.min)[x] || C.min[ret] == k)
                && (C.max[ret] == old(C.max)[x] || C.max[ret] == k)
                && Fresh(RefSetDiffF(C.repr[ret], old(C.repr)[x]), alloc, old(alloc))
                && (old(C.p)[x] == null ==> RefSetsEqual(Br, EmptyRefSet))
                && (old(C.p)[x] != null ==> RefSetsEqual(Br, EmptyRefSet[old(C.p)[x] := true])));
    // Framing conditions.
    ensures Frame_all(
        C.k, C.l, C.r, C.p,
        C.min, C.max, C.keys, C.repr,
        old(C.k), old(C.l), old(C.r), old(C.p), 
        old(C.min), old(C.max), old(C.keys), old(C.repr),
        if x == null then EmptyRefSet else old(C.repr)[x], old(alloc)
    );
{
    // Local variable declarations
    var leaf: Ref;
    var tmp: Ref;
    var oldl: Ref;
    var oldr: Ref;

    // Intermediate Expresssions
    var x_k: int; var x_l: Ref; var x_r: Ref;
    var x_l_min: int; var x_r_max: int; 
    var x_l_keys: KeySet; var x_l_repr: RefSet;
    var x_r_keys: KeySet; var x_r_repr: RefSet;

    call InAllocParam(x);

    if (x != null) {
        call x_k := Get_k(x);
        call x_l := Get_l(x);
        call x_r := Get_r(x);
    }
    if (x == null) {
        call leaf := Create(k);

        call Set_min(leaf, k);
        call Set_max(leaf, k);
        call Set_keys(leaf, EmptyKeySet[k := true]);
        call Set_repr(leaf, EmptyRefSet[leaf := true]);
        
        call AssertLCAndRemove(leaf);
        ret := leaf;
    } else if (k < x_k) {
        call IfNotBr_ThenLC(x_l);
        call IfNotBr_ThenLC(x_r);

        call tmp := BSTInsertContract(x_l, k);
        call x_l := Get_l(x);
        call x_r := Get_r(x);
        call IfNotBr_ThenLC(x_l);
        call IfNotBr_ThenLC(x_r);

        oldl := x_l;
        call Set_l(x, tmp);
        call Set_p(tmp, x);

        call x_l := Get_l(x);
        call x_r := Get_r(x);
        call x_k := Get_k(x);
        if (x_l != null) {
            call x_l_min := Get_min(x_l);
            call x_l_keys := Get_keys(x_l);
            call x_l_repr := Get_repr(x_l);
        }
        if (x_r != null) {
            call x_r_max := Get_max(x_r);
            call x_r_keys := Get_keys(x_r);
            call x_r_repr := Get_repr(x_r);
        }
        call Set_min(x, if x_l == null then x_k else x_l_min);
        call Set_max(x, if x_r == null then x_k else x_r_max);
        call Set_keys(x, 
            KeySetUnionF(
                (if x_l == null then EmptyKeySet else x_l_keys)[x_k := true],
                if x_r == null then EmptyKeySet else x_r_keys
            )
        );
        call Set_repr(x, 
            RefSetUnionF(
                (if x_l == null then EmptyRefSet else x_l_repr)[x := true],
                if x_r == null then EmptyRefSet else x_r_repr
            )
        );
        call Set_p(x, null);

        call AssertLCAndRemove(tmp);
        call AssertLCAndRemove(x);
        call AssertLCAndRemove(oldl);

        ret := x;
    } else {
        call IfNotBr_ThenLC(x_l);
        call IfNotBr_ThenLC(x_r);

        call tmp := BSTInsertContract(x_r, k);
        call x_l := Get_l(x);
        call x_r := Get_r(x);
        call IfNotBr_ThenLC(x_l);
        call IfNotBr_ThenLC(x_r);

        oldr := x_r;
        call Set_r(x, tmp);
        call Set_p(tmp, x);

        call x_l := Get_l(x);
        call x_r := Get_r(x);
        call x_k := Get_k(x);
        if (x_l != null) {
            call x_l_min := Get_min(x_l);
            call x_l_keys := Get_keys(x_l);
            call x_l_repr := Get_repr(x_l);
        }
        if (x_r != null) {
            call x_r_max := Get_max(x_r);
            call x_r_keys := Get_keys(x_r);
            call x_r_repr := Get_repr(x_r);
        }
        call Set_min(x, if x_l == null then x_k else x_l_min);
        call Set_max(x, if x_r == null then x_k else x_r_max);
        call Set_keys(x, 
            KeySetUnionF(
                (if x_l == null then EmptyKeySet else x_l_keys)[x_k := true],
                if x_r == null then EmptyKeySet else x_r_keys
            )
        );
        call Set_repr(x, 
            RefSetUnionF(
                (if x_l == null then EmptyRefSet else x_l_repr)[x := true],
                if x_r == null then EmptyRefSet else x_r_repr
            )
        );
        call Set_p(x, null);

        call AssertLCAndRemove(tmp);
        call AssertLCAndRemove(x);
        call AssertLCAndRemove(oldr);

        ret := x;
    }
}