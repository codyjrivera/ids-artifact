// Supporting Artifact for
// "Predictive Verification using Intrinsic Definitions of Data Structures"
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
                              x, alloc);
    requires x != null ==> !(C.keys[x])[k];
    modifies C.k, C.l, C.r, C.p, 
        C.min, C.max, C.keys,
        C.repr, C.black, C.black_height, Br, alloc;
    ensures RefSetSubset(old(alloc), alloc);
    ensures ret != null;
    ensures (LC(C.k, C.l, C.r, C.p, 
               C.min, C.max, C.keys,
               C.repr, C.black, C.black_height, 
               ret, alloc) ||
             LC_Trans_RedRed(C.k, C.l, C.r, C.p, 
               C.min, C.max, C.keys,
               C.repr, C.black, C.black_height, 
               ret, alloc));
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
                              x, alloc);
    requires x != null ==> !(C.keys[x])[k];
    modifies C.k, C.l, C.r, C.p, 
        C.min, C.max, C.keys,
        C.repr, C.black, C.black_height, Br, alloc;
    ensures RefSetSubset(old(alloc), alloc);
    ensures ret != null;
    ensures (LC(C.k, C.l, C.r, C.p, 
               C.min, C.max, C.keys,
               C.repr, C.black, C.black_height, 
               ret, alloc) ||
             LC_Trans_RedRed(C.k, C.l, C.r, C.p, 
               C.min, C.max, C.keys,
               C.repr, C.black, C.black_height, 
               ret, alloc));
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

    if (x == null) {
        call leaf := Create(k);

        call Set_black(leaf, false);
        call Set_min(leaf, k);
        call Set_max(leaf, k);
        call Set_keys(leaf, EmptyKeySet[C.k[leaf] := true]);
        call Set_repr(leaf, EmptyRefSet[leaf := true]);
        call Set_black_height(leaf, 0);
        
        call AssertLCAndRemove(leaf);
        ret := leaf;
    } else {
        if (k < C.k[x]) {
            if (C.l[x] != null) {
                call IfNotBr_ThenLC(C.l[x]);
            }
            if (C.r[x] != null) {
                call IfNotBr_ThenLC(C.r[x]);
            }

            call p := RBTInsertContract(C.l[x], k);

            if (C.l[x] != null && C.l[x] != p) {
                call IfNotBr_ThenLC(C.l[x]);
            }
            if (C.r[x] != null) {
                call IfNotBr_ThenLC(C.r[x]);
            }

            if (C.black[p]) {
                // assert {:split_here} true;
                oldl := C.l[x];
                call Set_l(x, p);
                call Set_p(p, x);

                call Set_min(x, if C.l[x] == null then C.k[x] else C.min[C.l[x]]);
                call Set_max(x, if C.r[x] == null then C.k[x] else C.max[C.r[x]]);
                call Set_keys(x, 
                    KeySetUnionF(
                        (if C.l[x] == null then EmptyKeySet else C.keys[C.l[x]])[C.k[x] := true],
                        if C.r[x] == null then EmptyKeySet else C.keys[C.r[x]]
                    )
                );
                call Set_repr(x, 
                    RefSetUnionF(
                        (if C.l[x] == null then EmptyRefSet else C.repr[C.l[x]])[x := true],
                        if C.r[x] == null then EmptyRefSet else C.repr[C.r[x]]
                    )
                );
                call Set_p(x, null);

                call AssertLCAndRemove(p);
                call AssertLCAndRemove(oldl);
                ret := x;
            } else {
                xr := C.r[x];

                if (xr != null && !C.black[xr]) {
                    oldl := C.l[x];

                    call Set_l(x, p);
                    call Set_p(p, x);

                    call Set_min(x, if C.l[x] == null then C.k[x] else C.min[C.l[x]]);
                    call Set_max(x, if C.r[x] == null then C.k[x] else C.max[C.r[x]]);
                    call Set_keys(x, 
                        KeySetUnionF(
                            (if C.l[x] == null then EmptyKeySet else C.keys[C.l[x]])[C.k[x] := true],
                            if C.r[x] == null then EmptyKeySet else C.keys[C.r[x]]
                        )
                    );
                    call Set_repr(x, 
                        RefSetUnionF(
                            (if C.l[x] == null then EmptyRefSet else C.repr[C.l[x]])[x := true],
                            if C.r[x] == null then EmptyRefSet else C.repr[C.r[x]]
                        )
                    );
                    call Set_p(x, null);

                    call Set_black(x, false);
                    call Set_black(p, true);
                    call Set_black_height(p, C.black_height[p] + 1);
                    call Set_black(xr, true);
                    call Set_black_height(xr, C.black_height[xr] + 1);

                    call AssertLCAndRemove(p);
                    call AssertLCAndRemove(xr);
                    call AssertLCAndRemove(oldl);

                    ret := x;
                } else {
                    pl := C.l[p];
                    pr := C.r[p];

                    if (pl != null) {
                        call IfNotBr_ThenLC(pl);
                    }
                    if (pr != null) {
                        call IfNotBr_ThenLC(pr);
                    }

                    if (pr != null && !C.black[pr]) {
                        assert {:focus} true;
                        prl := C.l[pr];
                        prr := C.r[pr];
                        if (prl != null) {
                            call IfNotBr_ThenLC(prl);
                        }
                        if (prr != null) {
                            call IfNotBr_ThenLC(prr);
                        }

                        call Set_r(p, prl);
                        if (prl != null) {
                            call Set_p(prl, p);
                        }
                        oldl := C.l[x];
                        call Set_l(x, prr);
                        if (prr != null) {
                            call Set_p(prr, x);
                        }
                        call Set_l(pr, p);
                        call Set_p(p, pr);
                        call Set_r(pr, x);
                        call Set_p(x, pr);
                        call Set_p(pr, null);

                        call Set_min(p, if C.l[p] == null then C.k[p] else C.min[C.l[p]]);
                        call Set_max(p, if C.r[p] == null then C.k[p] else C.max[C.r[p]]);
                        call Set_keys(p, 
                            KeySetUnionF(
                                (if C.l[p] == null then EmptyKeySet else C.keys[C.l[p]])[C.k[p] := true],
                                if C.r[p] == null then EmptyKeySet else C.keys[C.r[p]]
                            )
                        );
                        call Set_repr(p, 
                            RefSetUnionF(
                                (if C.l[p] == null then EmptyRefSet else C.repr[C.l[p]])[p := true],
                                if C.r[p] == null then EmptyRefSet else C.repr[C.r[p]]
                            )
                        );

                        call Set_min(x, if C.l[x] == null then C.k[x] else C.min[C.l[x]]);
                        call Set_max(x, if C.r[x] == null then C.k[x] else C.max[C.r[x]]);
                        call Set_keys(x, 
                            KeySetUnionF(
                                (if C.l[x] == null then EmptyKeySet else C.keys[C.l[x]])[C.k[x] := true],
                                if C.r[x] == null then EmptyKeySet else C.keys[C.r[x]]
                            )
                        );
                        call Set_repr(x, 
                            RefSetUnionF(
                                (if C.l[x] == null then EmptyRefSet else C.repr[C.l[x]])[x := true],
                                if C.r[x] == null then EmptyRefSet else C.repr[C.r[x]]
                            )
                        );
                        if (C.black[x]) {
                            call Set_black_height(x, C.black_height[x] - 1);
                        }
                        call Set_black(x, false);

                        call Set_min(pr, if C.l[pr] == null then C.k[pr] else C.min[C.l[pr]]);
                        call Set_max(pr, if C.r[pr] == null then C.k[pr] else C.max[C.r[pr]]);
                        call Set_keys(pr, 
                            KeySetUnionF(
                                (if C.l[pr] == null then EmptyKeySet else C.keys[C.l[pr]])[C.k[pr] := true],
                                if C.r[pr] == null then EmptyKeySet else C.keys[C.r[pr]]
                            )
                        );
                        call Set_repr(pr, 
                            RefSetUnionF(
                                (if C.l[pr] == null then EmptyRefSet else C.repr[C.l[pr]])[pr := true],
                                if C.r[pr] == null then EmptyRefSet else C.repr[C.r[pr]]
                            )
                        ); 
                        call Set_black(pr, true);
                        call Set_black_height(pr, C.black_height[pr] + 1);

                        call AssertLCAndRemove(prl);
                        call AssertLCAndRemove(prr);
                        call AssertLCAndRemove(p);
                        call AssertLCAndRemove(x);
                        call AssertLCAndRemove(oldl);

                        ret := pr;
                    } else if (pl != null && !C.black[pl]) {
                        assert {:focus} true;
                        call Set_r(p, x);
                        call Set_p(x, p);
                        oldl := C.l[x];
                        call Set_l(x, pr);
                        if (pr != null) {
                            call Set_p(pr, x);
                        }
                        call Set_p(p, null);

                        call Set_min(x, if C.l[x] == null then C.k[x] else C.min[C.l[x]]);
                        call Set_max(x, if C.r[x] == null then C.k[x] else C.max[C.r[x]]);
                        call Set_keys(x, 
                            KeySetUnionF(
                                (if C.l[x] == null then EmptyKeySet else C.keys[C.l[x]])[C.k[x] := true],
                                if C.r[x] == null then EmptyKeySet else C.keys[C.r[x]]
                            )
                        );
                        call Set_repr(x, 
                            RefSetUnionF(
                                (if C.l[x] == null then EmptyRefSet else C.repr[C.l[x]])[x := true],
                                if C.r[x] == null then EmptyRefSet else C.repr[C.r[x]]
                            )
                        );
                        if (C.black[x]) {
                            call Set_black_height(x, C.black_height[x] - 1);
                        }
                        call Set_black(x, false);

                        call Set_min(p, if C.l[p] == null then C.k[p] else C.min[C.l[p]]);
                        call Set_max(p, if C.r[p] == null then C.k[p] else C.max[C.r[p]]);
                        call Set_keys(p, 
                            KeySetUnionF(
                                (if C.l[p] == null then EmptyKeySet else C.keys[C.l[p]])[C.k[p] := true],
                                if C.r[p] == null then EmptyKeySet else C.keys[C.r[p]]
                            )
                        );
                        call Set_repr(p, 
                            RefSetUnionF(
                                (if C.l[p] == null then EmptyRefSet else C.repr[C.l[p]])[p := true],
                                if C.r[p] == null then EmptyRefSet else C.repr[C.r[p]]
                            )
                        );
                        call Set_black(p, true);
                        call Set_black_height(p, C.black_height[p] + 1);

                        call AssertLCAndRemove(pr);
                        call AssertLCAndRemove(x);
                        call AssertLCAndRemove(oldl);

                        ret := p;
                    } else {
                        // assert {:split_here} true;
                        oldl := C.l[x];
                        call Set_l(x, p);
                        call Set_p(p, x);

                        call Set_min(x, if C.l[x] == null then C.k[x] else C.min[C.l[x]]);
                        call Set_max(x, if C.r[x] == null then C.k[x] else C.max[C.r[x]]);
                        call Set_keys(x, 
                            KeySetUnionF(
                                (if C.l[x] == null then EmptyKeySet else C.keys[C.l[x]])[C.k[x] := true],
                                if C.r[x] == null then EmptyKeySet else C.keys[C.r[x]]
                            )
                        );
                        call Set_repr(x, 
                            RefSetUnionF(
                                (if C.l[x] == null then EmptyRefSet else C.repr[C.l[x]])[x := true],
                                if C.r[x] == null then EmptyRefSet else C.repr[C.r[x]]
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
            if (C.l[x] != null) {
                call IfNotBr_ThenLC(C.l[x]);
            }
            if (C.r[x] != null) {
                call IfNotBr_ThenLC(C.r[x]);
            }

            call p := RBTInsertContract(C.r[x], k);

            if (C.l[x] != null) {
                call IfNotBr_ThenLC(C.l[x]);
            }
            if (C.r[x] != null && C.r[x] != p) {
                call IfNotBr_ThenLC(C.r[x]);
            }

            if (C.black[p]) {
                oldr := C.r[x];
                call Set_r(x, p);
                call Set_p(p, x);

                call Set_min(x, if C.l[x] == null then C.k[x] else C.min[C.l[x]]);
                call Set_max(x, if C.r[x] == null then C.k[x] else C.max[C.r[x]]);
                call Set_keys(x, 
                    KeySetUnionF(
                        (if C.l[x] == null then EmptyKeySet else C.keys[C.l[x]])[C.k[x] := true],
                        if C.r[x] == null then EmptyKeySet else C.keys[C.r[x]]
                    )
                );
                call Set_repr(x, 
                    RefSetUnionF(
                        (if C.l[x] == null then EmptyRefSet else C.repr[C.l[x]])[x := true],
                        if C.r[x] == null then EmptyRefSet else C.repr[C.r[x]]
                    )
                );
                call Set_p(x, null);

                call AssertLCAndRemove(p);
                call AssertLCAndRemove(oldr);
                ret := x;
            } else {
                xl := C.l[x];

                if (xl != null && !C.black[xl]) {
                    oldr := C.r[x];
                    call Set_r(x, p);
                    call Set_p(p, x);

                    call Set_min(x, if C.l[x] == null then C.k[x] else C.min[C.l[x]]);
                    call Set_max(x, if C.r[x] == null then C.k[x] else C.max[C.r[x]]);
                    call Set_keys(x, 
                        KeySetUnionF(
                            (if C.l[x] == null then EmptyKeySet else C.keys[C.l[x]])[C.k[x] := true],
                            if C.r[x] == null then EmptyKeySet else C.keys[C.r[x]]
                        )
                    );
                    call Set_repr(x, 
                        RefSetUnionF(
                            (if C.l[x] == null then EmptyRefSet else C.repr[C.l[x]])[x := true],
                            if C.r[x] == null then EmptyRefSet else C.repr[C.r[x]]
                        )
                    );
                    call Set_p(x, null);

                    call Set_black(x, false);
                    call Set_black(p, true);
                    call Set_black_height(p, C.black_height[p] + 1);
                    call Set_black(xl, true);
                    call Set_black_height(xl, C.black_height[xl] + 1);

                    call AssertLCAndRemove(p);
                    call AssertLCAndRemove(xl);
                    call AssertLCAndRemove(oldr);
                    ret := x;
                } else {
                    pl := C.l[p];
                    pr := C.r[p];

                    if (pl != null) {
                        call IfNotBr_ThenLC(pl);
                    }
                    if (pr != null) {
                        call IfNotBr_ThenLC(pr);
                    }

                    if (pl != null && !C.black[pl]) {
                        assert {:focus} true;
                        pll := C.l[pl];
                        plr := C.r[pl];
                        if (pll != null) {
                            call IfNotBr_ThenLC(pll);
                        }
                        if (plr != null) {
                            call IfNotBr_ThenLC(plr);
                        }

                        call Set_l(p, plr);
                        if (plr != null) {
                            call Set_p(plr, p);
                        }
                        oldr := C.r[x];
                        call Set_r(x, pll);
                        if (pll != null) {
                            call Set_p(pll, x);
                        }
                        call Set_r(pl, p);
                        call Set_p(p, pl);
                        call Set_l(pl, x);
                        call Set_p(x, pl);
                        call Set_p(pl, null);

                        call Set_min(p, if C.l[p] == null then C.k[p] else C.min[C.l[p]]);
                        call Set_max(p, if C.r[p] == null then C.k[p] else C.max[C.r[p]]);
                        call Set_keys(p, 
                            KeySetUnionF(
                                (if C.l[p] == null then EmptyKeySet else C.keys[C.l[p]])[C.k[p] := true],
                                if C.r[p] == null then EmptyKeySet else C.keys[C.r[p]]
                            )
                        );
                        call Set_repr(p, 
                            RefSetUnionF(
                                (if C.l[p] == null then EmptyRefSet else C.repr[C.l[p]])[p := true],
                                if C.r[p] == null then EmptyRefSet else C.repr[C.r[p]]
                            )
                        );

                        call Set_min(x, if C.l[x] == null then C.k[x] else C.min[C.l[x]]);
                        call Set_max(x, if C.r[x] == null then C.k[x] else C.max[C.r[x]]);
                        call Set_keys(x, 
                            KeySetUnionF(
                                (if C.l[x] == null then EmptyKeySet else C.keys[C.l[x]])[C.k[x] := true],
                                if C.r[x] == null then EmptyKeySet else C.keys[C.r[x]]
                            )
                        );
                        call Set_repr(x, 
                            RefSetUnionF(
                                (if C.l[x] == null then EmptyRefSet else C.repr[C.l[x]])[x := true],
                                if C.r[x] == null then EmptyRefSet else C.repr[C.r[x]]
                            )
                        );
                        if (C.black[x]) {
                            call Set_black_height(x, C.black_height[x] - 1);
                        }
                        call Set_black(x, false);

                        call Set_min(pl, if C.l[pl] == null then C.k[pl] else C.min[C.l[pl]]);
                        call Set_max(pl, if C.r[pl] == null then C.k[pl] else C.max[C.r[pl]]);
                        call Set_keys(pl, 
                            KeySetUnionF(
                                (if C.l[pl] == null then EmptyKeySet else C.keys[C.l[pl]])[C.k[pl] := true],
                                if C.r[pl] == null then EmptyKeySet else C.keys[C.r[pl]]
                            )
                        );
                        call Set_repr(pl, 
                            RefSetUnionF(
                                (if C.l[pl] == null then EmptyRefSet else C.repr[C.l[pl]])[pl := true],
                                if C.r[pl] == null then EmptyRefSet else C.repr[C.r[pl]]
                            )
                        ); 
                        call Set_black(pl, true);
                        call Set_black_height(pl, C.black_height[pl] + 1);

                        call AssertLCAndRemove(pll);
                        call AssertLCAndRemove(plr);
                        call AssertLCAndRemove(p);
                        call AssertLCAndRemove(x);
                        call AssertLCAndRemove(oldr);

                        ret := pl;
                    } else if (pr != null && !C.black[pr]) {
                        assert {:focus} true;
                        call Set_l(p, x);
                        call Set_p(x, p);
                        oldr := C.r[x];
                        call Set_r(x, pl);
                        if (pl != null) {
                            call Set_p(pl, x);
                        }
                        call Set_p(p, null);

                        call Set_min(x, if C.l[x] == null then C.k[x] else C.min[C.l[x]]);
                        call Set_max(x, if C.r[x] == null then C.k[x] else C.max[C.r[x]]);
                        call Set_keys(x, 
                            KeySetUnionF(
                                (if C.l[x] == null then EmptyKeySet else C.keys[C.l[x]])[C.k[x] := true],
                                if C.r[x] == null then EmptyKeySet else C.keys[C.r[x]]
                            )
                        );
                        call Set_repr(x, 
                            RefSetUnionF(
                                (if C.l[x] == null then EmptyRefSet else C.repr[C.l[x]])[x := true],
                                if C.r[x] == null then EmptyRefSet else C.repr[C.r[x]]
                            )
                        );
                        if (C.black[x]) {
                            call Set_black_height(x, C.black_height[x] - 1);
                        }
                        call Set_black(x, false);

                        call Set_min(p, if C.l[p] == null then C.k[p] else C.min[C.l[p]]);
                        call Set_max(p, if C.r[p] == null then C.k[p] else C.max[C.r[p]]);
                        call Set_keys(p, 
                            KeySetUnionF(
                                (if C.l[p] == null then EmptyKeySet else C.keys[C.l[p]])[C.k[p] := true],
                                if C.r[p] == null then EmptyKeySet else C.keys[C.r[p]]
                            )
                        );
                        call Set_repr(p, 
                            RefSetUnionF(
                                (if C.l[p] == null then EmptyRefSet else C.repr[C.l[p]])[p := true],
                                if C.r[p] == null then EmptyRefSet else C.repr[C.r[p]]
                            )
                        );
                        call Set_black(p, true);
                        call Set_black_height(p, C.black_height[p] + 1);

                        call AssertLCAndRemove(pl);
                        call AssertLCAndRemove(x);
                        call AssertLCAndRemove(oldr);
                        
                        ret := p;
                    } else {
                        oldr := C.r[x];
                        call Set_r(x, p);
                        call Set_p(p, x);
                        
                        call Set_min(x, if C.l[x] == null then C.k[x] else C.min[C.l[x]]);
                        call Set_max(x, if C.r[x] == null then C.k[x] else C.max[C.r[x]]);
                        call Set_keys(x, 
                            KeySetUnionF(
                                (if C.l[x] == null then EmptyKeySet else C.keys[C.l[x]])[C.k[x] := true],
                                if C.r[x] == null then EmptyKeySet else C.keys[C.r[x]]
                            )
                        );
                        call Set_repr(x, 
                            RefSetUnionF(
                                (if C.l[x] == null then EmptyRefSet else C.repr[C.l[x]])[x := true],
                                if C.r[x] == null then EmptyRefSet else C.repr[C.r[x]]
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