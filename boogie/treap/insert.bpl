// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions"
// by Adithya Murali, Cody Rivera, and P. Madhusudan.
// 
// Artifact by Cody Rivera, 2023-2024. 
//
// Verification of Treap Insert.

procedure TreapInsertContract(x: Ref, k: int, prio: int)
    returns (ret: Ref);
    requires Br == EmptyRefSet;
    requires x != null ==> LC(C.k, C.prio, C.l, C.r, C.p, 
                                C.min, C.max, C.keys, C.repr,
                                x);
    requires x != null ==> !(C.keys[x])[k];
    modifies C.k, C.prio, C.l, C.r, C.p,
        C.min, C.max, C.keys,
        C.repr, Br, alloc;
    ensures RefSetSubset(old(alloc), alloc);
    ensures ret != null;
    ensures LC(C.k, C.prio, C.l, C.r, C.p, 
                C.min, C.max, C.keys, C.repr,
                ret);
    ensures C.p[ret] == null;
    ensures x != null ==> (ret == x || C.l[ret] == x || C.r[ret] == x);
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
                && (C.l[ret] != null ==> C.prio[C.l[ret]] <= old(C.prio)[x])
                && (C.r[ret] != null ==> C.prio[C.r[ret]] <= old(C.prio)[x])
                && Fresh(RefSetDiffF(C.repr[ret], old(C.repr)[x]), alloc, old(alloc))
                && (old(C.p)[x] == null ==> RefSetsEqual(Br, EmptyRefSet))
                && (old(C.p)[x] != null ==> RefSetsEqual(Br, EmptyRefSet[old(C.p)[x] := true])));
    // Framing conditions.
    ensures Frame_all(
        C.k, C.prio, C.l, C.r, C.p,
        C.min, C.max, C.keys, C.repr,
        old(C.k), old(C.prio), old(C.l), old(C.r), old(C.p), 
        old(C.min), old(C.max), old(C.keys), old(C.repr),
        if x == null then EmptyRefSet else old(C.repr)[x], old(alloc)
    );

procedure TreapInsert(x: Ref, k: int, prio: int)
    returns (ret: Ref)
    requires Br == EmptyRefSet;
    requires x != null ==> LC(C.k, C.prio, C.l, C.r, C.p, 
                                C.min, C.max, C.keys, C.repr,
                                x);
    requires x != null ==> !(C.keys[x])[k];
    modifies C.k, C.prio, C.l, C.r, C.p,
        C.min, C.max, C.keys,
        C.repr, Br, alloc;
    ensures RefSetSubset(old(alloc), alloc);
    ensures ret != null;
    ensures LC(C.k, C.prio, C.l, C.r, C.p, 
                C.min, C.max, C.keys, C.repr,
                ret);
    ensures C.p[ret] == null;
    ensures x != null ==> (ret == x || C.l[ret] == x || C.r[ret] == x);
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
                && (C.l[ret] != null ==> C.prio[C.l[ret]] <= old(C.prio)[x])
                && (C.r[ret] != null ==> C.prio[C.r[ret]] <= old(C.prio)[x])
                && Fresh(RefSetDiffF(C.repr[ret], old(C.repr)[x]), alloc, old(alloc))
                && (old(C.p)[x] == null ==> RefSetsEqual(Br, EmptyRefSet))
                && (old(C.p)[x] != null ==> RefSetsEqual(Br, EmptyRefSet[old(C.p)[x] := true])));
    // Framing conditions.
    ensures Frame_all(
        C.k, C.prio, C.l, C.r, C.p,
        C.min, C.max, C.keys, C.repr,
        old(C.k), old(C.prio), old(C.l), old(C.r), old(C.p), 
        old(C.min), old(C.max), old(C.keys), old(C.repr),
        if x == null then EmptyRefSet else old(C.repr)[x], old(alloc)
    );
{
    // Local variable declarations
    var leaf: Ref;
    var tmp: Ref;
    var oldl: Ref;
    var oldr: Ref;
    var lr: Ref;
    var rl: Ref;

    // Intermediate Expresssions
    var x_k: int; var x_l: Ref; var x_r: Ref;
    var x_l_min: int; var x_r_max: int; 
    var x_l_keys: KeySet; var x_l_repr: RefSet;
    var x_r_keys: KeySet; var x_r_repr: RefSet;
    var tmp_prio: int; var x_prio: int;
    var old_x_l: Ref; var old_x_r: Ref;
    var tmp_k: int; var tmp_l: Ref; var tmp_r: Ref;
    var tmp_l_min: int; var tmp_r_max: int; 
    var tmp_l_keys: KeySet; var tmp_l_repr: RefSet;
    var tmp_r_keys: KeySet; var tmp_r_repr: RefSet;

    call InAllocParam(x);

    if (x != null) {
        call x_k := Get_k(x);
        call x_l := Get_l(x);
        call x_r := Get_r(x);
        old_x_l := x_l;
        old_x_r := x_r;
    }
    if (x == null) {
        call leaf := Create(k, prio);

        call Set_min(leaf, k);
        call Set_max(leaf, k);
        call Set_keys(leaf, EmptyKeySet[k := true]);
        call Set_repr(leaf, EmptyRefSet[leaf := true]);
        
        call AssertLCAndRemove(leaf);
        ret := leaf;
    } else if (k < x_k) {
        call IfNotBr_ThenLC(x_l);
        call IfNotBr_ThenLC(x_r);

        call tmp := TreapInsertContract(x_l, k, prio);

        call tmp_prio := Get_prio(tmp);
        call x_prio := Get_prio(x);

        if (tmp_prio <= x_prio) {
            call x_l := Get_l(x);
            call IfNotBr_ThenLC(x_l);

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
            call Set_p(x, null);

            call AssertLCAndRemove(tmp);
            call AssertLCAndRemove(x);
            call AssertLCAndRemove(oldl);

            ret := x;
        } else {
            call tmp_l := Get_l(tmp);
            call tmp_r := Get_r(tmp);
            call IfNotBr_ThenLC(tmp_l);
            call IfNotBr_ThenLC(tmp_r);
            call lr := Get_r(tmp);

            call Set_l(x, lr);
            call AssertLCAndRemove(old_x_l);
            if (lr != null) {
                call Set_p(lr, x);
            }

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

            call Set_r(tmp, x);
            call Set_p(x, tmp);
            
            call tmp_l := Get_l(tmp);
            call tmp_r := Get_r(tmp);
            call tmp_k := Get_k(tmp);
            if (tmp_l != null) {
                call tmp_l_min := Get_min(tmp_l);
                call tmp_l_keys := Get_keys(tmp_l);
                call tmp_l_repr := Get_repr(tmp_l);
            }
            if (tmp_r != null) {
                call tmp_r_max := Get_max(tmp_r);
                call tmp_r_keys := Get_keys(tmp_r);
                call tmp_r_repr := Get_repr(tmp_r);
            }
            call Set_min(tmp, if tmp_l == null then tmp_k else tmp_l_min);
            call Set_max(tmp, if tmp_r == null then tmp_k else tmp_r_max);
            call Set_keys(tmp, 
                KeySetUnionF(
                    (if tmp_l == null then EmptyKeySet else tmp_l_keys)[tmp_k := true],
                    if tmp_r == null then EmptyKeySet else tmp_r_keys
                )
            );
            call Set_repr(tmp, 
                RefSetUnionF(
                    (if tmp_l == null then EmptyRefSet else tmp_l_repr)[tmp := true],
                    if tmp_r == null then EmptyRefSet else tmp_r_repr
                )
            );

            call AssertLCAndRemove(lr);
            call AssertLCAndRemove(x);
            call AssertLCAndRemove(tmp);

            ret := tmp;
        }
    } else {
        call IfNotBr_ThenLC(x_l);
        call IfNotBr_ThenLC(x_r);

        call tmp := TreapInsertContract(x_r, k, prio);

        call tmp_prio := Get_prio(tmp);
        call x_prio := Get_prio(x);

        if (tmp_prio <= x_prio) {
            call x_r := Get_r(x);
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
            call Set_p(x, null);

            call AssertLCAndRemove(tmp);
            call AssertLCAndRemove(x);
            call AssertLCAndRemove(oldr);

            ret := x;
        } else {
            call tmp_l := Get_l(tmp);
            call tmp_r := Get_r(tmp);
            call IfNotBr_ThenLC(tmp_l);
            call IfNotBr_ThenLC(tmp_r);
            call rl := Get_l(tmp);

            call Set_r(x, rl);
            call AssertLCAndRemove(old_x_r);
            if (rl != null) {
                call Set_p(rl, x);
            }

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

            call Set_l(tmp, x);
            call Set_p(x, tmp);
            
            call tmp_l := Get_l(tmp);
            call tmp_r := Get_r(tmp);
            call tmp_k := Get_k(tmp);
            if (tmp_l != null) {
                call tmp_l_min := Get_min(tmp_l);
                call tmp_l_keys := Get_keys(tmp_l);
                call tmp_l_repr := Get_repr(tmp_l);
            }
            if (tmp_r != null) {
                call tmp_r_max := Get_max(tmp_r);
                call tmp_r_keys := Get_keys(tmp_r);
                call tmp_r_repr := Get_repr(tmp_r);
            }
            call Set_min(tmp, if tmp_l == null then tmp_k else tmp_l_min);
            call Set_max(tmp, if tmp_r == null then tmp_k else tmp_r_max);
            call Set_keys(tmp, 
                KeySetUnionF(
                    (if tmp_l == null then EmptyKeySet else tmp_l_keys)[tmp_k := true],
                    if tmp_r == null then EmptyKeySet else tmp_r_keys
                )
            );
            call Set_repr(tmp, 
                RefSetUnionF(
                    (if tmp_l == null then EmptyRefSet else tmp_l_repr)[tmp := true],
                    if tmp_r == null then EmptyRefSet else tmp_r_repr
                )
            );

            call AssertLCAndRemove(rl);
            call AssertLCAndRemove(x);
            call AssertLCAndRemove(tmp);

            ret := tmp;
        }
    }
}