// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions"
// by Adithya Murali, Cody Rivera, and P. Madhusudan.
// 
// Artifact by Cody Rivera, 2023. 
//
// Verification of Red-Black Tree Insert.

procedure RBTInsertContract(x: Ref, k: int)
    returns (ret: Ref);
    requires Br == EmptyRefSet;
    requires x != null ==> LC(C.k, C.l, C.r, C.p, 
                              C.min, C.max, C.keys,
                              C.repr, C.black, C.black_height, 
                              x);
    requires x != null ==> !(C.keys[x])[k];
    modifies C.k, C.l, C.r, C.p, 
        C.min, C.max, C.keys,
        C.repr, C.black, C.black_height, Br, alloc;
    ensures RefSetSubset(old(alloc), alloc);
    ensures ret != null;
    ensures (LC(C.k, C.l, C.r, C.p, 
               C.min, C.max, C.keys,
               C.repr, C.black, C.black_height, 
               ret) ||
             LC_Trans_RedRed(C.k, C.l, C.r, C.p, 
               C.min, C.max, C.keys,
               C.repr, C.black, C.black_height, 
               ret));
    ensures C.p[ret] == null;
    ensures x != null && x != ret ==> C.p[x] != old(C.p)[x];
    ensures (x == null ==>
                KeySetsEqual(C.keys[ret], EmptyKeySet[k := true])
                && C.min[ret] == k
                && C.max[ret] == k
                && C.black_height[ret] == 0
                && Fresh(C.repr[ret], alloc, old(alloc))
                && RefSetSubset(Br, EmptyRefSet[ret := true]));
    ensures (x != null ==>
                KeySetsEqual(C.keys[ret], (old(C.keys)[x])[k := true])
                && (C.min[ret] == old(C.min)[x] || C.min[ret] == k)
                && (C.max[ret] == old(C.max)[x] || C.max[ret] == k)
                && C.black_height[ret] == old(C.black_height)[x]
                && (C.black[ret] ||
                        (!C.black[ret] && ((C.l[ret] == null || C.black[C.l[ret]] || C.r[ret] == null || C.black[C.r[ret]])
                        && (!old(C.black)[x] || ((C.l[ret] == null || C.black[C.l[ret]]) && (C.r[ret] == null || C.black[C.r[ret]]))))))
                && Fresh(RefSetDiffF(C.repr[ret], old(C.repr)[x]), alloc, old(alloc))
                && (old(C.p)[x] == null ==> RefSetSubset(Br, EmptyRefSet[ret := true]))
                && (old(C.p)[x] != null ==> RefSetSubset(Br, (EmptyRefSet[ret := true])[old(C.p)[x] := true])));
    // Framing conditions.
    ensures Frame_all(
        C.k, C.l, C.r, C.p, 
        C.min, C.max, C.keys,
        C.repr, C.black, C.black_height,
        old(C.k), old(C.l), old(C.r), old(C.p), 
        old(C.min), old(C.max), old(C.keys),
        old(C.repr), old(C.black), old(C.black_height),
        if x == null then EmptyRefSet else old(C.repr)[x], old(alloc)
    );

procedure RBTInsert(x: Ref, k: int)
    returns (ret: Ref)
    requires Br == EmptyRefSet;
    requires x != null ==> LC(C.k, C.l, C.r, C.p, 
                              C.min, C.max, C.keys,
                              C.repr, C.black, C.black_height, 
                              x);
    requires x != null ==> !(C.keys[x])[k];
    modifies C.k, C.l, C.r, C.p, 
        C.min, C.max, C.keys,
        C.repr, C.black, C.black_height, Br, alloc;
    ensures RefSetSubset(old(alloc), alloc);
    ensures ret != null;
    ensures (LC(C.k, C.l, C.r, C.p, 
               C.min, C.max, C.keys,
               C.repr, C.black, C.black_height, 
               ret) ||
             LC_Trans_RedRed(C.k, C.l, C.r, C.p, 
               C.min, C.max, C.keys,
               C.repr, C.black, C.black_height, 
               ret));
    ensures C.p[ret] == null;
    ensures x != null && x != ret ==> C.p[x] != old(C.p)[x];
    ensures (x == null ==>
                KeySetsEqual(C.keys[ret], EmptyKeySet[k := true])
                && C.min[ret] == k
                && C.max[ret] == k
                && C.black_height[ret] == 0
                && Fresh(C.repr[ret], alloc, old(alloc))
                && RefSetSubset(Br, EmptyRefSet[ret := true]));
    ensures (x != null ==>
                KeySetsEqual(C.keys[ret], (old(C.keys)[x])[k := true])
                && (C.min[ret] == old(C.min)[x] || C.min[ret] == k)
                && (C.max[ret] == old(C.max)[x] || C.max[ret] == k)
                && C.black_height[ret] == old(C.black_height)[x]
                && (C.black[ret] ||
                        (!C.black[ret] && ((C.l[ret] == null || C.black[C.l[ret]] || C.r[ret] == null || C.black[C.r[ret]])
                        && (!old(C.black)[x] || ((C.l[ret] == null || C.black[C.l[ret]]) && (C.r[ret] == null || C.black[C.r[ret]]))))))
                && Fresh(RefSetDiffF(C.repr[ret], old(C.repr)[x]), alloc, old(alloc))
                && (old(C.p)[x] == null ==> RefSetSubset(Br, EmptyRefSet[ret := true]))
                && (old(C.p)[x] != null ==> RefSetSubset(Br, (EmptyRefSet[ret := true])[old(C.p)[x] := true])));
    // Framing conditions.
    ensures Frame_all(
        C.k, C.l, C.r, C.p, 
        C.min, C.max, C.keys,
        C.repr, C.black, C.black_height,
        old(C.k), old(C.l), old(C.r), old(C.p), 
        old(C.min), old(C.max), old(C.keys),
        old(C.repr), old(C.black), old(C.black_height),
        if x == null then EmptyRefSet else old(C.repr)[x], old(alloc)
    );
{
    // Local variable declarations
    var p: Ref;
    var pl: Ref;
    var pr: Ref;
    var pll: Ref;
    var plr: Ref;
    var prl: Ref;
    var prr: Ref;
    var xl: Ref;
    var xr: Ref;
    var oldl: Ref;
    var oldr: Ref;
    var leaf: Ref;

    // Intermediate Expresssions
    var x_k: int;
    var x_l: Ref;
    var x_r: Ref;
    var x_black: bool;
    var x_black_height: int;
    var p_black: bool;
    var p_black_height: int;
    var x_l_min: int;
    var x_l_keys: KeySet;
    var x_l_repr: RefSet;
    var x_r_max: int;
    var x_r_keys: KeySet;
    var x_r_repr: RefSet;
    var xr_black: bool;
    var xr_black_height: int;
    var p_l: Ref;
    var p_r: Ref;
    var p_k: int;
    var p_l_min: int;
    var p_l_keys: KeySet;
    var p_l_repr: RefSet;
    var p_r_max: int;
    var p_r_keys: KeySet;
    var p_r_repr: RefSet;
    var pl_black: bool;
    var pr_black: bool;
    var pr_l: Ref;
    var pr_r: Ref;
    var pr_k: int;
    var pr_l_min: int;
    var pr_l_keys: KeySet;
    var pr_l_repr: RefSet;
    var pr_r_max: int;
    var pr_r_keys: KeySet;
    var pr_r_repr: RefSet;
    var pr_black_height: int;
    var xl_black: bool;
    var xl_black_height: int;
    var pl_l: Ref;
    var pl_r: Ref;
    var pl_k: int;
    var pl_l_min: int;
    var pl_l_keys: KeySet;
    var pl_l_repr: RefSet;
    var pl_r_max: int;
    var pl_r_keys: KeySet;
    var pl_r_repr: RefSet;
    var pl_black_height: int;

    call InAllocParam(x);
    if (x == null) {
        call leaf := Create(k);

        call Set_black(leaf, false);
        call Set_min(leaf, k);
        call Set_max(leaf, k);
        call Set_keys(leaf, EmptyKeySet[k := true]);
        call Set_repr(leaf, EmptyRefSet[leaf := true]);
        call Set_black_height(leaf, 0);
        
        call AssertLCAndRemove(leaf);
        ret := leaf;
    } else {
        call x_k := Get_k(x);
        if (k < x_k) {
            call x_l := Get_l(x);
            call x_r := Get_r(x);

            call IfNotBr_ThenLC(x_l);
            call IfNotBr_ThenLC(x_r);

            call p := RBTInsertContract(x_l, k);

            call x_l := Get_l(x);
            call x_r := Get_r(x);            
            call IfNotBr_ThenLC(x_l);
            call IfNotBr_ThenLC(x_r);

            call p_black := Get_black(p);
            if (p_black) {
                call x_l := Get_l(x);
                oldl := x_l;
                call Set_l(x, p);
                call Set_p(p, x);

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

                call AssertLCAndRemove(p);
                call AssertLCAndRemove(oldl);
                ret := x;
            } else {
                call x_r := Get_r(x);
                xr := x_r;

                if (x_r != null) {
                    call xr_black := Get_black(xr);
                }
                if (xr != null && !xr_black) {
                    call x_l := Get_l(x);
                    oldl := x_l;

                    call Set_l(x, p);
                    call Set_p(p, x);

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

                    call Set_black(x, false);
                    call Set_black(p, true);
                    call p_black_height := Get_black_height(p);
                    call Set_black_height(p, p_black_height + 1);
                    call Set_black(xr, true);
                    call xr_black_height := Get_black_height(xr);
                    call Set_black_height(xr, xr_black_height + 1);

                    call AssertLCAndRemove(p);
                    call AssertLCAndRemove(xr);
                    call AssertLCAndRemove(oldl);

                    ret := x;
                } else {
                    call p_l := Get_l(p);
                    call p_r := Get_r(p);

                    pl := p_l;
                    pr := p_r;

                    call IfNotBr_ThenLC(pl);
                    call IfNotBr_ThenLC(pr);

                    if (pr != null) {
                        call pr_black := Get_black(pr);
                    }
                    if (pl != null) {
                        call pl_black := Get_black(pl);
                    }
                    if (pr != null && !pr_black) {
                        call pr_l := Get_l(pr);
                        call pr_r := Get_r(pr);
                        prl := pr_l;
                        prr := pr_r;
                        call IfNotBr_ThenLC(prl);
                        call IfNotBr_ThenLC(prr);

                        call Set_r(p, prl);
                        if (prl != null) {
                            call Set_p(prl, p);
                        }
                        call x_l := Get_l(x);
                        oldl := x_l;
                        call Set_l(x, prr);
                        if (prr != null) {
                            call Set_p(prr, x);
                        }
                        call Set_l(pr, p);
                        call Set_p(p, pr);
                        call Set_r(pr, x);
                        call Set_p(x, pr);
                        call Set_p(pr, null);

                        call p_l := Get_l(p);
                        call p_r := Get_r(p);
                        call p_k := Get_k(p);
                        if (p_l != null) {
                            call p_l_min := Get_min(p_l);
                            call p_l_keys := Get_keys(p_l);
                            call p_l_repr := Get_repr(p_l);
                        }
                        if (p_r != null) {
                            call p_r_max := Get_max(p_r);
                            call p_r_keys := Get_keys(p_r);
                            call p_r_repr := Get_repr(p_r);
                        }
                        call Set_min(p, if p_l == null then p_k else p_l_min);
                        call Set_max(p, if p_r == null then p_k else p_r_max);
                        call Set_keys(p, 
                            KeySetUnionF(
                                (if p_l == null then EmptyKeySet else p_l_keys)[p_k := true],
                                if p_r == null then EmptyKeySet else p_r_keys
                            )
                        );
                        call Set_repr(p, 
                            RefSetUnionF(
                                (if p_l == null then EmptyRefSet else p_l_repr)[p := true],
                                if p_r == null then EmptyRefSet else p_r_repr
                            )
                        );

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
                        call x_black := Get_black(x);
                        call x_black_height := Get_black_height(x);
                        if (x_black) {
                            call Set_black_height(x, x_black_height - 1);
                        }
                        call Set_black(x, false);

                        call pr_l := Get_l(pr);
                        call pr_r := Get_r(pr);
                        call pr_k := Get_k(pr);
                        if (pr_l != null) {
                            call pr_l_min := Get_min(pr_l);
                            call pr_l_keys := Get_keys(pr_l);
                            call pr_l_repr := Get_repr(pr_l);
                        }
                        if (pr_r != null) {
                            call pr_r_max := Get_max(pr_r);
                            call pr_r_keys := Get_keys(pr_r);
                            call pr_r_repr := Get_repr(pr_r);
                        }
                        call Set_min(pr, if pr_l == null then pr_k else pr_l_min);
                        call Set_max(pr, if pr_r == null then pr_k else pr_r_max);
                        call Set_keys(pr, 
                            KeySetUnionF(
                                (if pr_l == null then EmptyKeySet else pr_l_keys)[pr_k := true],
                                if pr_r == null then EmptyKeySet else pr_r_keys
                            )
                        );
                        call Set_repr(pr, 
                            RefSetUnionF(
                                (if pr_l == null then EmptyRefSet else pr_l_repr)[pr := true],
                                if pr_r == null then EmptyRefSet else pr_r_repr
                            )
                        ); 
                        call Set_black(pr, true);
                        call pr_black_height := Get_black_height(pr);
                        call Set_black_height(pr, pr_black_height + 1);

                        call AssertLCAndRemove(prl);
                        call AssertLCAndRemove(prr);
                        call AssertLCAndRemove(p);
                        call AssertLCAndRemove(x);
                        call AssertLCAndRemove(oldl);

                        ret := pr;
                    } else if (pl != null && !pl_black) {
                        call Set_r(p, x);
                        call Set_p(x, p);
                        call x_l := Get_l(x);
                        oldl := x_l;
                        call Set_l(x, pr);
                        if (pr != null) {
                            call Set_p(pr, x);
                        }
                        call Set_p(p, null);

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

                        call x_black := Get_black(x);
                        call x_black_height := Get_black_height(x);
                        if (x_black) {
                            call Set_black_height(x, x_black_height - 1);
                        }
                        call Set_black(x, false);

                        call p_l := Get_l(p);
                        call p_r := Get_r(p);
                        call p_k := Get_k(p);
                        if (p_l != null) {
                            call p_l_min := Get_min(p_l);
                            call p_l_keys := Get_keys(p_l);
                            call p_l_repr := Get_repr(p_l);
                        }
                        if (p_r != null) {
                            call p_r_max := Get_max(p_r);
                            call p_r_keys := Get_keys(p_r);
                            call p_r_repr := Get_repr(p_r);
                        }
                        call Set_min(p, if p_l == null then p_k else p_l_min);
                        call Set_max(p, if p_r == null then p_k else p_r_max);
                        call Set_keys(p, 
                            KeySetUnionF(
                                (if p_l == null then EmptyKeySet else p_l_keys)[p_k := true],
                                if p_r == null then EmptyKeySet else p_r_keys
                            )
                        );
                        call Set_repr(p, 
                            RefSetUnionF(
                                (if p_l == null then EmptyRefSet else p_l_repr)[p := true],
                                if p_r == null then EmptyRefSet else p_r_repr
                            )
                        );
                        call Set_black(p, true);
                        call p_black_height := Get_black_height(p);
                        call Set_black_height(p, p_black_height + 1);

                        call AssertLCAndRemove(pr);
                        call AssertLCAndRemove(x);
                        call AssertLCAndRemove(oldl);

                        ret := p;
                    } else {
                        call x_l := Get_l(x);
                        oldl := x_l;
                        call Set_l(x, p);
                        call Set_p(p, x);

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

                        call AssertLCAndRemove(p);
                        call AssertLCAndRemove(oldl);
                        ret := x;
                    }
                }
            }
        } else {
            call x_l := Get_l(x);
            call x_r := Get_r(x);

            call IfNotBr_ThenLC(x_l);
            call IfNotBr_ThenLC(x_r);

            call p := RBTInsertContract(x_r, k);

            call x_l := Get_l(x);
            call x_r := Get_r(x);            
            call IfNotBr_ThenLC(x_l);
            call IfNotBr_ThenLC(x_r);

            call p_black := Get_black(p);
            if (p_black) {
                call x_r := Get_r(x);
                oldr := x_r;
                call Set_r(x, p);
                call Set_p(p, x);

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

                call AssertLCAndRemove(p);
                call AssertLCAndRemove(oldr);
                ret := x;
            } else {
                call x_l := Get_l(x);
                xl := x_l;

                if (xl != null) {
                    call xl_black := Get_black(xl);
                }
                if (xl != null && !xl_black) {
                    call x_r := Get_r(x);
                    oldr := x_r;

                    call Set_r(x, p);
                    call Set_p(p, x);

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

                    call Set_black(x, false);
                    call Set_black(p, true);
                    call p_black_height := Get_black_height(p);
                    call Set_black_height(p, p_black_height + 1);
                    call Set_black(xl, true);
                    call xl_black_height := Get_black_height(xl);
                    call Set_black_height(xl, xl_black_height + 1);

                    call AssertLCAndRemove(p);
                    call AssertLCAndRemove(xl);
                    call AssertLCAndRemove(oldr);

                    ret := x;
                } else {
                    call p_l := Get_l(p);
                    call p_r := Get_r(p);

                    pl := p_l;
                    pr := p_r;

                    call IfNotBr_ThenLC(pl);
                    call IfNotBr_ThenLC(pr);

                    if (pr != null) {
                        call pr_black := Get_black(pr);
                    }
                    if (pl != null) {
                        call pl_black := Get_black(pl);
                    }
                    if (pl != null && !pl_black) {
                        call pl_l := Get_l(pl);
                        call pl_r := Get_r(pl);
                        pll := pl_l;
                        plr := pl_r;
                        call IfNotBr_ThenLC(pll);
                        call IfNotBr_ThenLC(plr);

                        call Set_l(p, plr);
                        if (plr != null) {
                            call Set_p(plr, p);
                        }
                        call x_r := Get_r(x);
                        oldr := x_r;
                        call Set_r(x, pll);
                        if (pll != null) {
                            call Set_p(pll, x);
                        }
                        call Set_r(pl, p);
                        call Set_p(p, pl);
                        call Set_l(pl, x);
                        call Set_p(x, pl);
                        call Set_p(pl, null);

                        call p_l := Get_l(p);
                        call p_r := Get_r(p);
                        call p_k := Get_k(p);
                        if (p_l != null) {
                            call p_l_min := Get_min(p_l);
                            call p_l_keys := Get_keys(p_l);
                            call p_l_repr := Get_repr(p_l);
                        }
                        if (p_r != null) {
                            call p_r_max := Get_max(p_r);
                            call p_r_keys := Get_keys(p_r);
                            call p_r_repr := Get_repr(p_r);
                        }
                        call Set_min(p, if p_l == null then p_k else p_l_min);
                        call Set_max(p, if p_r == null then p_k else p_r_max);
                        call Set_keys(p, 
                            KeySetUnionF(
                                (if p_l == null then EmptyKeySet else p_l_keys)[p_k := true],
                                if p_r == null then EmptyKeySet else p_r_keys
                            )
                        );
                        call Set_repr(p, 
                            RefSetUnionF(
                                (if p_l == null then EmptyRefSet else p_l_repr)[p := true],
                                if p_r == null then EmptyRefSet else p_r_repr
                            )
                        );

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
                        call x_black := Get_black(x);
                        call x_black_height := Get_black_height(x);
                        if (x_black) {
                            call Set_black_height(x, x_black_height - 1);
                        }
                        call Set_black(x, false);

                        call pl_l := Get_l(pl);
                        call pl_r := Get_r(pl);
                        call pl_k := Get_k(pl);
                        if (pl_l != null) {
                            call pl_l_min := Get_min(pl_l);
                            call pl_l_keys := Get_keys(pl_l);
                            call pl_l_repr := Get_repr(pl_l);
                        }
                        if (pl_r != null) {
                            call pl_r_max := Get_max(pl_r);
                            call pl_r_keys := Get_keys(pl_r);
                            call pl_r_repr := Get_repr(pl_r);
                        }
                        call Set_min(pl, if pl_l == null then pl_k else pl_l_min);
                        call Set_max(pl, if pl_r == null then pl_k else pl_r_max);
                        call Set_keys(pl, 
                            KeySetUnionF(
                                (if pl_l == null then EmptyKeySet else pl_l_keys)[pl_k := true],
                                if pl_r == null then EmptyKeySet else pl_r_keys
                            )
                        );
                        call Set_repr(pl, 
                            RefSetUnionF(
                                (if pl_l == null then EmptyRefSet else pl_l_repr)[pl := true],
                                if pl_r == null then EmptyRefSet else pl_r_repr
                            )
                        ); 
                        call Set_black(pl, true);
                        call pl_black_height := Get_black_height(pl);
                        call Set_black_height(pl, pl_black_height + 1);

                        call AssertLCAndRemove(pll);
                        call AssertLCAndRemove(plr);
                        call AssertLCAndRemove(p);
                        call AssertLCAndRemove(x);
                        call AssertLCAndRemove(oldr);

                        ret := pl;
                    } else if (pr != null && !pr_black) {
                        call Set_l(p, x);
                        call Set_p(x, p);
                        call x_r := Get_r(x);
                        oldr := x_r;
                        call Set_r(x, pl);
                        if (pl != null) {
                            call Set_p(pl, x);
                        }
                        call Set_p(p, null);

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

                        call x_black := Get_black(x);
                        call x_black_height := Get_black_height(x);
                        if (x_black) {
                            call Set_black_height(x, x_black_height - 1);
                        }
                        call Set_black(x, false);

                        call p_l := Get_l(p);
                        call p_r := Get_r(p);
                        call p_k := Get_k(p);
                        if (p_l != null) {
                            call p_l_min := Get_min(p_l);
                            call p_l_keys := Get_keys(p_l);
                            call p_l_repr := Get_repr(p_l);
                        }
                        if (p_r != null) {
                            call p_r_max := Get_max(p_r);
                            call p_r_keys := Get_keys(p_r);
                            call p_r_repr := Get_repr(p_r);
                        }
                        call Set_min(p, if p_l == null then p_k else p_l_min);
                        call Set_max(p, if p_r == null then p_k else p_r_max);
                        call Set_keys(p, 
                            KeySetUnionF(
                                (if p_l == null then EmptyKeySet else p_l_keys)[p_k := true],
                                if p_r == null then EmptyKeySet else p_r_keys
                            )
                        );
                        call Set_repr(p, 
                            RefSetUnionF(
                                (if p_l == null then EmptyRefSet else p_l_repr)[p := true],
                                if p_r == null then EmptyRefSet else p_r_repr
                            )
                        );
                        call Set_black(p, true);
                        call p_black_height := Get_black_height(p);
                        call Set_black_height(p, p_black_height + 1);

                        call AssertLCAndRemove(pl);
                        call AssertLCAndRemove(x);
                        call AssertLCAndRemove(oldr);

                        ret := p;
                    } else {
                        call x_r := Get_r(x);
                        oldr := x_r;
                        call Set_r(x, p);
                        call Set_p(p, x);

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

                        call AssertLCAndRemove(p);
                        call AssertLCAndRemove(oldr);
                        ret := x;
                    }
                }
            }
        }
    }
}