// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions"
// by Anonymous Authors.
// 
// Artifact by Anonymous Author, 2023-2024. 
//
// Verification of RBT Insert.

include "red-black-tree.dfy"

method RBTInsert(ghost Br: set<RBTNode>, x: RBTNode?, k: int) 
    returns (ghost Br': set<RBTNode>, ret: RBTNode)
    requires Br == {}
    requires x != null ==> x.LC()
    requires x != null ==> k !in x.keys
    modifies if x == null then {} else x.repr
    decreases if x == null then {} else x.repr
    ensures ret.LC() || ret.LC_Trans_RedRed()
    ensures ret.p == null
    ensures x != null && x != ret ==> x.p != old(x.p)
    ensures (x == null ==>
                ret.keys == {k}
                && ret.min == k == ret.max
                && ret.black_height == 0
                && fresh(ret.repr)
                && Br' <= {ret})
    ensures (x != null ==>
                ret.keys == old(x.keys) + {k}
                && (ret.min == old(x.min) || ret.min == k)
                && (ret.max == old(x.max) || ret.max == k)
                && ret.black_height == old(x.black_height)
                && (ret.black || 
                        (!ret.black && ((ret.l == null || ret.l.black || ret.r == null || ret.r.black)
                        && (!old(x.black) || ((ret.l == null || ret.l.black) && (ret.r == null || ret.r.black))))))
                && fresh(ret.repr - old(x.repr))
                && (old(x.p) == null ==> Br' <= {ret})
                && (old(x.p) != null ==> Br' <= {ret, old(x.p)}))
{
    Br' := Br;
    if (x == null) {
        var leaf;
        Br', leaf := RBTNode.Create(Br', k);
        Br' := leaf.Set_black(Br', false);
        Br' := leaf.Set_min(Br', k);
        Br' := leaf.Set_max(Br', k);
        Br' := leaf.Set_keys(Br', {leaf.k});
        Br' := leaf.Set_repr(Br', {leaf});
        Br' := leaf.Set_black_height(Br', 0);
        //assert leaf.LC();
	//Br' := Br' - {leaf};
        Br' := (if (leaf.LC()) then Br'-{leaf} else Br);
	// Br' := AssertLCAndRemove(Br', leaf);
        ret := leaf;
    } else if (k < x.k) {
        if (x.l != null) {
            IfNotBr_ThenLC(Br', x.l);
        }
        if (x.r != null) {
            IfNotBr_ThenLC(Br', x.r);
        }
        var p;
        Br', p := RBTInsert(Br', x.l, k);
        if (x.l != null && x.l != p) {
            IfNotBr_ThenLC(Br', x.l);
        }
        if (x.r != null) {
            IfNotBr_ThenLC(Br', x.r);
        }

        if p.black {
            ghost var oldl := x.l;
            Br' := x.Set_l(Br', p);
            Br' := p.Set_p(Br', x);

            Br' := x.Set_min(Br', if x.l == null then x.k else x.l.min);
            Br' := x.Set_max(Br', if x.r == null then x.k else x.r.max);
            Br' := x.Set_keys(Br', (if x.l == null then {} else x.l.keys) 
                                        + {x.k} + (if x.r == null then {} else x.r.keys));
            Br' := x.Set_repr(Br', (if x.l == null then {} else x.l.repr) 
                                        + {x} + (if x.r == null then {} else x.r.repr));

            Br' := x.Set_p(Br', null);

	    //assert p.LC();
            Br' := (if (p.LC()) then Br'-{p} else Br);
            //assert oldl.LC();
            Br' := (if (oldl != null && oldl.LC()) then Br'-{oldl} else Br);
            ret := x;
        } else {
            var xr := x.r;

            if xr != null && !xr.black {
                ghost var oldl := x.l;
                Br' := x.Set_l(Br', p);
                Br' := p.Set_p(Br', x);

                Br' := x.Set_min(Br', if x.l == null then x.k else x.l.min);
                Br' := x.Set_max(Br', if x.r == null then x.k else x.r.max);
                Br' := x.Set_keys(Br', (if x.l == null then {} else x.l.keys) 
                                            + {x.k} + (if x.r == null then {} else x.r.keys));
                Br' := x.Set_repr(Br', (if x.l == null then {} else x.l.repr) 
                                            + {x} + (if x.r == null then {} else x.r.repr));
                Br' := x.Set_p(Br', null);

                Br' := x.Set_black(Br', false);
                Br' := p.Set_black(Br', true);
                Br' := p.Set_black_height(Br', p.black_height + 1);
                Br' := xr.Set_black(Br', true);
                Br' := xr.Set_black_height(Br', xr.black_height + 1);

	        Br' := (if (p.LC()) then Br'-{p} else Br);
	        Br' := (if (xr != null && xr.LC()) then Br'-{xr} else Br);
	        Br' := (if (oldl != null && oldl.LC()) then Br'-{oldl} else Br);
                ret := x;
            } else {
                var pl := p.l;
                var pr := p.r;

                if pl != null {
                    IfNotBr_ThenLC(Br', pl);
                }
                if pr != null {
                    IfNotBr_ThenLC(Br', pr);
                }

                if pr != null && !pr.black {
                    var prl := pr.l;
                    var prr := pr.r;
                    if prl != null {
                        IfNotBr_ThenLC(Br', prl);
                    }
                    if prr != null {
                        IfNotBr_ThenLC(Br', prr);
                    }
                    
                    Br' := p.Set_r(Br', prl);
                    if prl != null {
                        Br' := prl.Set_p(Br', p);
                    }
                    ghost var oldl := x.l;
                    Br' := x.Set_l(Br', prr);
                    if prr != null {
                        Br' := prr.Set_p(Br', x);
                    }
                    Br' := pr.Set_l(Br', p);
                    Br' := p.Set_p(Br', pr);
                    Br' := pr.Set_r(Br', x);
                    Br' := x.Set_p(Br', pr);
                    Br' := pr.Set_p(Br', null);

                    Br' := p.Set_min(Br', if p.l == null then p.k else p.l.min);
                    Br' := p.Set_max(Br', if p.r == null then p.k else p.r.max);
                    Br' := p.Set_keys(Br', (if p.l == null then {} else p.l.keys) 
                                            + {p.k} + (if p.r == null then {} else p.r.keys));
                    Br' := p.Set_repr(Br', (if p.l == null then {} else p.l.repr) 
                                            + {p} + (if p.r == null then {} else p.r.repr));

                    Br' := x.Set_min(Br', if x.l == null then x.k else x.l.min);
                    Br' := x.Set_max(Br', if x.r == null then x.k else x.r.max);
                    Br' := x.Set_keys(Br', (if x.l == null then {} else x.l.keys) 
                                            + {x.k} + (if x.r == null then {} else x.r.keys));
                    Br' := x.Set_repr(Br', (if x.l == null then {} else x.l.repr) 
                                            + {x} + (if x.r == null then {} else x.r.repr));
                    if x.black {
                        Br' := x.Set_black_height(Br', x.black_height - 1);
                    }
                    Br' := x.Set_black(Br', false);

                    Br' := pr.Set_min(Br', if pr.l == null then pr.k else pr.l.min);
                    Br' := pr.Set_max(Br', if pr.r == null then pr.k else pr.r.max);
                    Br' := pr.Set_keys(Br', (if pr.l == null then {} else pr.l.keys) 
                                            + {pr.k} + (if pr.r == null then {} else pr.r.keys));
                    Br' := pr.Set_repr(Br', (if pr.l == null then {} else pr.l.repr) 
                                            + {pr} + (if pr.r == null then {} else pr.r.repr));
                    Br' := pr.Set_black(Br', true);
                    Br' := pr.Set_black_height(Br', pr.black_height + 1);

   		    Br' := (if (prl != null && prl.LC()) then Br'-{prl} else Br);
		    Br' := (if (prr != null && prr.LC()) then Br'-{prr} else Br);
   		    Br' := (if (p.LC()) then Br'-{p} else Br);
   		    Br' := (if (x != null && x.LC()) then Br'-{x} else Br);
   		    Br' := (if (oldl != null && oldl.LC()) then Br'-{oldl} else Br);

                    //Br' := AddToBr(Br', pr); // If we accidentally fixed pr.

                    ret := pr;
                } else if pl != null && !pl.black {
                    Br' := p.Set_r(Br', x);
                    Br' := x.Set_p(Br', p);
                    ghost var oldl := x.l;
                    Br' := x.Set_l(Br', pr);
                    if pr != null {
                        Br' := pr.Set_p(Br', x);
                    }
                    Br' := p.Set_p(Br', null);

                    Br' := x.Set_min(Br', if x.l == null then x.k else x.l.min);
                    Br' := x.Set_max(Br', if x.r == null then x.k else x.r.max);
                    Br' := x.Set_keys(Br', (if x.l == null then {} else x.l.keys) 
                                            + {x.k} + (if x.r == null then {} else x.r.keys));
                    Br' := x.Set_repr(Br', (if x.l == null then {} else x.l.repr) 
                                            + {x} + (if x.r == null then {} else x.r.repr));
                    if x.black {
                        Br' := x.Set_black_height(Br', x.black_height - 1);
                    }
                    Br' := x.Set_black(Br', false);

                    Br' := p.Set_min(Br', if p.l == null then p.k else p.l.min);
                    Br' := p.Set_max(Br', if p.r == null then p.k else p.r.max);
                    Br' := p.Set_keys(Br', (if p.l == null then {} else p.l.keys) 
                                            + {p.k} + (if p.r == null then {} else p.r.keys));
                    Br' := p.Set_repr(Br', (if p.l == null then {} else p.l.repr) 
                                            + {p} + (if p.r == null then {} else p.r.repr));
                    Br' := p.Set_black(Br', true);
                    Br' := p.Set_black_height(Br', p.black_height + 1);

		    Br' := (if (pr != null && pr.LC()) then Br'-{pr} else Br);
		    Br' := (if (x != null && x.LC()) then Br'-{x} else Br);
		    Br' := (if (oldl != null && oldl.LC()) then Br'-{oldl} else Br);

                    //Br' := AddToBr(Br', p); // If we accidentally fixed p.

                    ret := p;
                } else {
                    ghost var oldl := x.l;
                    Br' := x.Set_l(Br', p);
                    Br' := p.Set_p(Br', x);

                    Br' := x.Set_min(Br', if x.l == null then x.k else x.l.min);
                    Br' := x.Set_max(Br', if x.r == null then x.k else x.r.max);
                    Br' := x.Set_keys(Br', (if x.l == null then {} else x.l.keys) 
                                            + {x.k} + (if x.r == null then {} else x.r.keys));
                    Br' := x.Set_repr(Br', (if x.l == null then {} else x.l.repr) 
                                            + {x} + (if x.r == null then {} else x.r.repr));
                    Br' := x.Set_p(Br', null);

    		    Br' := (if (p.LC()) then Br'-{p} else Br);
    		    Br' := (if (oldl != null && oldl.LC()) then Br'-{oldl} else Br);

                    ret := x;
                }
            }
        }
    } else {
        if (x.l != null) {
            IfNotBr_ThenLC(Br', x.l);
        }
        if (x.r != null) {
            IfNotBr_ThenLC(Br', x.r);
        }
        var p;
        Br', p := RBTInsert(Br', x.r, k);
        if (x.l != null) {
            IfNotBr_ThenLC(Br', x.l);
        }
        if (x.r != null && x.r != p) {
            IfNotBr_ThenLC(Br', x.r);
        }

        if p.black {
            ghost var oldr := x.r;
            Br' := x.Set_r(Br', p);
            Br' := p.Set_p(Br', x);

            Br' := x.Set_min(Br', if x.l == null then x.k else x.l.min);
            Br' := x.Set_max(Br', if x.r == null then x.k else x.r.max);
            Br' := x.Set_keys(Br', (if x.l == null then {} else x.l.keys) 
                                        + {x.k} + (if x.r == null then {} else x.r.keys));
            Br' := x.Set_repr(Br', (if x.l == null then {} else x.l.repr) 
                                        + {x} + (if x.r == null then {} else x.r.repr));

            Br' := x.Set_p(Br', null);

   	    Br' := (if (p.LC()) then Br'-{p} else Br);
   	    Br' := (if (oldr.LC()) then Br'-{oldr} else Br);

            ret := x;
        } else {
            var xl := x.l;

            if xl != null && !xl.black {
                ghost var oldr := x.r;
                Br' := x.Set_r(Br', p);
                Br' := p.Set_p(Br', x);

                Br' := x.Set_min(Br', if x.l == null then x.k else x.l.min);
                Br' := x.Set_max(Br', if x.r == null then x.k else x.r.max);
                Br' := x.Set_keys(Br', (if x.l == null then {} else x.l.keys) 
                                            + {x.k} + (if x.r == null then {} else x.r.keys));
                Br' := x.Set_repr(Br', (if x.l == null then {} else x.l.repr) 
                                            + {x} + (if x.r == null then {} else x.r.repr));
                Br' := x.Set_p(Br', null);

                Br' := x.Set_black(Br', false);
                Br' := p.Set_black(Br', true);
                Br' := p.Set_black_height(Br', p.black_height + 1);
                Br' := xl.Set_black(Br', true);
                Br' := xl.Set_black_height(Br', xl.black_height + 1);

		Br' := (if (p.LC()) then Br'-{p} else Br);
		Br' := (if (xl != null && xl.LC()) then Br'-{xl} else Br);
		Br' := (if (oldr != null && oldr.LC()) then Br'-{oldr} else Br);

		ret := x;
            } else {
                var pl := p.l;
                var pr := p.r;

                if pl != null {
                    IfNotBr_ThenLC(Br', pl);
                }
                if pr != null {
                    IfNotBr_ThenLC(Br', pr);
                }

                if pl != null && !pl.black {
                    var pll := pl.l;
                    var plr := pl.r;
                    if pll != null {
                        IfNotBr_ThenLC(Br', pll);
                    }
                    if plr != null {
                        IfNotBr_ThenLC(Br', plr);
                    }
                    
                    Br' := p.Set_l(Br', plr);
                    if plr != null {
                        Br' := plr.Set_p(Br', p);
                    }
                    ghost var oldr := x.r;
                    Br' := x.Set_r(Br', pll);
                    if pll != null {
                        Br' := pll.Set_p(Br', x);
                    }
                    Br' := pl.Set_r(Br', p);
                    Br' := p.Set_p(Br', pl);
                    Br' := pl.Set_l(Br', x);
                    Br' := x.Set_p(Br', pl);
                    Br' := pl.Set_p(Br', null);

                    Br' := p.Set_min(Br', if p.l == null then p.k else p.l.min);
                    Br' := p.Set_max(Br', if p.r == null then p.k else p.r.max);
                    Br' := p.Set_keys(Br', (if p.l == null then {} else p.l.keys) 
                                            + {p.k} + (if p.r == null then {} else p.r.keys));
                    Br' := p.Set_repr(Br', (if p.l == null then {} else p.l.repr) 
                                            + {p} + (if p.r == null then {} else p.r.repr));

                    Br' := x.Set_min(Br', if x.l == null then x.k else x.l.min);
                    Br' := x.Set_max(Br', if x.r == null then x.k else x.r.max);
                    Br' := x.Set_keys(Br', (if x.l == null then {} else x.l.keys) 
                                            + {x.k} + (if x.r == null then {} else x.r.keys));
                    Br' := x.Set_repr(Br', (if x.l == null then {} else x.l.repr) 
                                            + {x} + (if x.r == null then {} else x.r.repr));
                    if x.black {
                        Br' := x.Set_black_height(Br', x.black_height - 1);
                    }
                    Br' := x.Set_black(Br', false);

                    Br' := pl.Set_min(Br', if pl.l == null then pl.k else pl.l.min);
                    Br' := pl.Set_max(Br', if pl.r == null then pl.k else pl.r.max);
                    Br' := pl.Set_keys(Br', (if pl.l == null then {} else pl.l.keys) 
                                            + {pl.k} + (if pl.r == null then {} else pl.r.keys));
                    Br' := pl.Set_repr(Br', (if pl.l == null then {} else pl.l.repr) 
                                            + {pl} + (if pl.r == null then {} else pl.r.repr));
                    Br' := pl.Set_black(Br', true);
                    Br' := pl.Set_black_height(Br', pl.black_height + 1);


		    Br' := (if (pll != null && pll.LC()) then Br'-{pll} else Br);
		    Br' := (if (plr != null && plr.LC()) then Br'-{plr} else Br);
		    Br' := (if (p.LC()) then Br'-{p} else Br);
		    Br' := (if (x != null && x.LC()) then Br'-{x} else Br);
		    Br' := (if (oldr != null && oldr.LC()) then Br'-{oldr} else Br);

                    //Br' := AddToBr(Br', pl); // If we accidentally fixed pr.

                    ret := pl;
                } else if pr != null && !pr.black {
                    Br' := p.Set_l(Br', x);
                    Br' := x.Set_p(Br', p);
                    ghost var oldr := x.r;
                    Br' := x.Set_r(Br', pl);
                    if pl != null {
                        Br' := pl.Set_p(Br', x);
                    }
                    Br' := p.Set_p(Br', null);

                    Br' := x.Set_min(Br', if x.l == null then x.k else x.l.min);
                    Br' := x.Set_max(Br', if x.r == null then x.k else x.r.max);
                    Br' := x.Set_keys(Br', (if x.l == null then {} else x.l.keys) 
                                            + {x.k} + (if x.r == null then {} else x.r.keys));
                    Br' := x.Set_repr(Br', (if x.l == null then {} else x.l.repr) 
                                            + {x} + (if x.r == null then {} else x.r.repr));
                    if x.black {
                        Br' := x.Set_black_height(Br', x.black_height - 1);
                    }
                    Br' := x.Set_black(Br', false);

                    Br' := p.Set_min(Br', if p.l == null then p.k else p.l.min);
                    Br' := p.Set_max(Br', if p.r == null then p.k else p.r.max);
                    Br' := p.Set_keys(Br', (if p.l == null then {} else p.l.keys) 
                                            + {p.k} + (if p.r == null then {} else p.r.keys));
                    Br' := p.Set_repr(Br', (if p.l == null then {} else p.l.repr) 
                                            + {p} + (if p.r == null then {} else p.r.repr));
                    Br' := p.Set_black(Br', true);
                    Br' := p.Set_black_height(Br', p.black_height + 1);

		    Br' := (if (pl != null && pl.LC()) then Br'-{pl} else Br);
		    Br' := (if (x != null && x.LC()) then Br'-{x} else Br);
		    Br' := (if (oldr != null && oldr.LC()) then Br'-{oldr} else Br);

                    ret := p;
                } else {
                    ghost var oldr := x.r;
                    Br' := x.Set_r(Br', p);
                    Br' := p.Set_p(Br', x);

                    Br' := x.Set_min(Br', if x.l == null then x.k else x.l.min);
                    Br' := x.Set_max(Br', if x.r == null then x.k else x.r.max);
                    Br' := x.Set_keys(Br', (if x.l == null then {} else x.l.keys) 
                                            + {x.k} + (if x.r == null then {} else x.r.keys));
                    Br' := x.Set_repr(Br', (if x.l == null then {} else x.l.repr) 
                                            + {x} + (if x.r == null then {} else x.r.repr));
                    Br' := x.Set_p(Br', null);

    		    Br' := (if (p.LC()) then Br'-{p} else Br);
    		    Br' := (if (oldr != null && oldr.LC()) then Br'-{oldr} else Br);

                    ret := x;
                }
            }
        }
    }
}