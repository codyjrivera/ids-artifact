// Supporting Artifact for
// "Predictive Verification using Intrinsic Definitions of Data Structures"
// by Adithya Murali, Cody Rivera, and P. Madhusudan.
// 
// Artifact by Cody Rivera, 2023. 
//
// Verification of AVL Insert.

function {:inline} GetHeight(height: [Ref]int, x: Ref) returns (int)
{
    if x == null then 0 else height[x]
}

function {:inline} MaxInt(x: int, y: int) returns (int)
{
    if x > y then x else y
}

procedure AVLBalanceContract(x: Ref) returns (ret: Ref);
    requires x != null;
    requires RefSetsDisjoint(Br, (C.repr[x])[x := false]);
    requires LC_Trans_Unbalanced(C.k, C.l, C.r, C.p, C.height, 
                                    C.min, C.max, C.keys, C.repr,
                                    x);
    modifies Br, C.k, C.l, C.r, C.p, C.height, 
                C.min, C.max, C.keys, C.repr;
    ensures ret != null;
    ensures x != ret ==> (
        C.p[x] != null
        && C.p[x] != old(C.p)[x]
        && (C.repr[ret])[C.p[x]]
        && (C.l[x] != null ==> (C.repr[ret])[C.l[x]])
        && (C.r[x] != null ==> (C.repr[ret])[C.r[x]])
    );
    ensures LC(C.k, C.l, C.r, C.p, C.height, 
                C.min, C.max, C.keys, C.repr,
                ret);
    ensures C.p[ret] == null;
    ensures KeySetsEqual(C.keys[ret], old(C.keys)[x]);
    ensures RefSetsEqual(C.repr[ret], old(C.repr)[x]);
    ensures C.min[ret] == old(C.min)[x];
    ensures C.max[ret] == old(C.max)[x];
    ensures (C.height[ret] == old(C.height)[x] || C.height[ret] == old(C.height)[x] - 1);
    ensures (
        (-1 <= GetHeight(old(C.height), old(C.r)[x]) - GetHeight(old(C.height), old(C.l)[x])
        && GetHeight(old(C.height), old(C.r)[x]) - GetHeight(old(C.height), old(C.l)[x]) <= 1)
        ==>
        C.height[ret] == old(C.height)[x]
    );
    ensures old(C.p)[x] == null ==> RefSetsEqual(Br, old(Br)[x := false]);
    ensures old(C.p)[x] != null ==> RefSetsEqual(Br, (old(Br)[x := false])[old(C.p)[x] := true]);
    // Framing conditions.
    ensures Frame_all(
        C.k, C.l, C.r, C.p, C.height,
        C.min, C.max, C.keys, C.repr,
        old(C.k), old(C.l), old(C.r), old(C.p), old(C.height), 
        old(C.min), old(C.max), old(C.keys), old(C.repr),
        old(C.repr)[x], old(alloc)
    );

procedure AVLInsertContract(x: Ref, k: int)
    returns (ret: Ref);
    requires Br == EmptyRefSet;
    requires x != null ==> LC(C.k, C.l, C.r, C.p, C.height, 
                                C.min, C.max, C.keys, C.repr,
                                x);
    requires x != null ==> !(C.keys[x])[k];
    modifies C.k, C.l, C.r, C.p, C.height,
        C.min, C.max, C.keys,
        C.repr, Br, alloc;
    ensures RefSetSubset(old(alloc), alloc);
    ensures ret != null;
    ensures LC(C.k, C.l, C.r, C.p, C.height, 
                C.min, C.max, C.keys, C.repr,
                ret);
    ensures C.p[ret] == null;
    ensures (x != null && x != ret) ==> C.p[x] != old(C.p)[x];
    ensures (x == null ==>
                KeySetsEqual(C.keys[ret], EmptyKeySet[k := true])
                && C.min[ret] == k
                && C.max[ret] == k
                && C.height[ret] == 1
                && Fresh(C.repr[ret], alloc, old(alloc))
                && RefSetsEqual(Br, EmptyRefSet));
    ensures (x != null ==>
                KeySetsEqual(C.keys[ret], (old(C.keys)[x])[k := true])
                && (C.min[ret] == old(C.min)[x] || C.min[ret] == k)
                && (C.max[ret] == old(C.max)[x] || C.max[ret] == k)
                && (C.height[ret] == old(C.height)[x]
                    || C.height[ret] == old(C.height)[x] + 1)
                && Fresh(RefSetDiffF(C.repr[ret], old(C.repr)[x]), alloc, old(alloc))
                && (old(C.p)[x] == null ==> RefSetsEqual(Br, EmptyRefSet))
                && (old(C.p)[x] != null ==> RefSetsEqual(Br, EmptyRefSet[old(C.p)[x] := true])));
    // Framing conditions.
    ensures Frame_all(
        C.k, C.l, C.r, C.p, C.height,
        C.min, C.max, C.keys, C.repr,
        old(C.k), old(C.l), old(C.r), old(C.p), old(C.height), 
        old(C.min), old(C.max), old(C.keys), old(C.repr),
        if x == null then EmptyRefSet else old(C.repr)[x], old(alloc)
    );

procedure AVLInsert(x: Ref, k: int)
    returns (ret: Ref)
    requires Br == EmptyRefSet;
    requires x != null ==> LC(C.k, C.l, C.r, C.p, C.height, 
                                C.min, C.max, C.keys, C.repr,
                                x);
    requires x != null ==> !(C.keys[x])[k];
    modifies C.k, C.l, C.r, C.p, C.height,
        C.min, C.max, C.keys,
        C.repr, Br, alloc;
    ensures RefSetSubset(old(alloc), alloc);
    ensures ret != null;
    ensures LC(C.k, C.l, C.r, C.p, C.height, 
                C.min, C.max, C.keys, C.repr,
                ret);
    ensures C.p[ret] == null;
    ensures (x != null && x != ret) ==> C.p[x] != old(C.p)[x];
    ensures (x == null ==>
                KeySetsEqual(C.keys[ret], EmptyKeySet[k := true])
                && C.min[ret] == k
                && C.max[ret] == k
                && C.height[ret] == 1
                && Fresh(C.repr[ret], alloc, old(alloc))
                && RefSetsEqual(Br, EmptyRefSet));
    ensures (x != null ==>
                KeySetsEqual(C.keys[ret], (old(C.keys)[x])[k := true])
                && (C.min[ret] == old(C.min)[x] || C.min[ret] == k)
                && (C.max[ret] == old(C.max)[x] || C.max[ret] == k)
                && (C.height[ret] == old(C.height)[x]
                    || C.height[ret] == old(C.height)[x] + 1)
                && Fresh(RefSetDiffF(C.repr[ret], old(C.repr)[x]), alloc, old(alloc))
                && (old(C.p)[x] == null ==> RefSetsEqual(Br, EmptyRefSet))
                && (old(C.p)[x] != null ==> RefSetsEqual(Br, EmptyRefSet[old(C.p)[x] := true]))
                );
    // Framing conditions.
    ensures Frame_all(
        C.k, C.l, C.r, C.p, C.height,
        C.min, C.max, C.keys, C.repr,
        old(C.k), old(C.l), old(C.r), old(C.p), old(C.height), 
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
        call Set_height(leaf, 1);
        
        call AssertLCAndRemove(leaf);
        ret := leaf;
    } else if (k < x_k) {
        call IfNotBr_ThenLC(x_l);
        call IfNotBr_ThenLC(x_r);

        call tmp := AVLInsertContract(x_l, k);
        call x_l := Get_l(x);
        call x_r := Get_r(x);
        call IfNotBr_ThenLC(x_l);
        call IfNotBr_ThenLC(x_r);

        call oldl := Get_l(x);
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
        call Set_height(x, MaxInt(GetHeight(C.height, x_l), GetHeight(C.height, x_r)) + 1);
        call Set_p(x, null);

        call AssertLCAndRemove(tmp);
        call AssertLCAndRemove(oldl);

        call ret := AVLBalanceContract(x);
    } else {
        call IfNotBr_ThenLC(x_l);
        call IfNotBr_ThenLC(x_r);

        call tmp := AVLInsertContract(x_r, k);
        call x_l := Get_l(x);
        call x_r := Get_r(x);
        call IfNotBr_ThenLC(x_l);
        call IfNotBr_ThenLC(x_r);

        call oldr := Get_r(x);
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
        call Set_height(x, MaxInt(GetHeight(C.height, x_l), GetHeight(C.height, x_r)) + 1);
        call Set_p(x, null);

        call AssertLCAndRemove(tmp);
        call AssertLCAndRemove(oldr);

        call ret := AVLBalanceContract(x);
    }
}