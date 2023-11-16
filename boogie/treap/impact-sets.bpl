// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions of Datastructures"
// by Anonymous Authors.
// 
// Artifact by Anonymous Author, 2023. 
//
// Impact set verification for Treaps.

procedure Check_Create(arb: Ref, k: int, prio: int)
    modifies Br, alloc, C.k, C.prio, C.l, C.r, C.p, 
              C.min, C.max, C.keys,
              C.repr;
{
    var node: Ref;

    assume LC(C.k, C.prio, C.l, C.r, C.p, 
              C.min, C.max, C.keys,
              C.repr,
              arb);
    assume arb != null;
    call InAllocParam(arb);
    call node := Create(k, prio);
    assert LC(C.k, C.prio, C.l, C.r, C.p, 
              C.min, C.max, C.keys,
              C.repr,
              arb);
}

procedure Check_Set_k(x: Ref, arb: Ref, k: int)
    modifies C.k;
{
    assume x != null;
    assume LC(C.k, C.prio, C.l, C.r, C.p, 
              C.min, C.max, C.keys,
              C.repr, 
              arb);
    assume arb != null;
    assume arb != x;
    assume arb != C.p[x];
    C.k := C.k[x := k];
    assert LC(C.k, C.prio, C.l, C.r, C.p, 
              C.min, C.max, C.keys,
              C.repr, 
              arb);
}

procedure Check_Set_prio(x: Ref, arb: Ref, prio: int)
    modifies C.prio;
{
    assume x != null;
    assume LC(C.k, C.prio, C.l, C.r, C.p, 
              C.min, C.max, C.keys,
              C.repr, 
              arb);
    assume arb != null;
    assume arb != x;
    assume arb != C.p[x];
    C.prio := C.prio[x := prio];
    assert LC(C.k, C.prio, C.l, C.r, C.p, 
              C.min, C.max, C.keys,
              C.repr, 
              arb);
}

procedure Check_Set_l(x: Ref, arb: Ref, l: Ref)
    modifies C.l;
{
    assume x != null;
    assume LC(C.k, C.prio, C.l, C.r, C.p, 
              C.min, C.max, C.keys,
              C.repr, 
              arb);
    assume arb != null;
    assume arb != x;
    assume arb != C.l[x];
    C.l := C.l[x := l];
    assert LC(C.k, C.prio, C.l, C.r, C.p, 
              C.min, C.max, C.keys,
              C.repr, 
              arb);
}

procedure Check_Set_r(x: Ref, arb: Ref, r: Ref)
    modifies C.r;
{
    assume x != null;
    assume LC(C.k, C.prio, C.l, C.r, C.p, 
              C.min, C.max, C.keys,
              C.repr, 
              arb);
    assume arb != null;
    assume arb != x;
    assume arb != C.r[x];
    C.r := C.r[x := r];
    assert LC(C.k, C.prio, C.l, C.r, C.p, 
              C.min, C.max, C.keys,
              C.repr, 
              arb);
}

procedure Check_Set_p(x: Ref, arb: Ref, p: Ref)
    modifies C.p;
{
    assume x != null;
    assume LC(C.k, C.prio, C.l, C.r, C.p, 
              C.min, C.max, C.keys,
              C.repr, 
              arb);
    assume arb != null;
    assume arb != x;
    assume arb != C.p[x];
    C.p := C.p[x := p];
    assert LC(C.k, C.prio, C.l, C.r, C.p, 
              C.min, C.max, C.keys,
              C.repr, 
              arb);
}

procedure Check_Set_min(x: Ref, arb: Ref, min: int)
    modifies C.min;
{
    assume x != null;
    assume LC(C.k, C.prio, C.l, C.r, C.p, 
              C.min, C.max, C.keys,
              C.repr, 
              arb);
    assume arb != null;
    assume arb != x;
    assume arb != C.p[x];
    C.min := C.min[x := min];
    assert LC(C.k, C.prio, C.l, C.r, C.p, 
              C.min, C.max, C.keys,
              C.repr, 
              arb);
}

procedure Check_Set_max(x: Ref, arb: Ref, max: int)
    modifies C.max;
{
    assume x != null;
    assume LC(C.k, C.prio, C.l, C.r, C.p, 
              C.min, C.max, C.keys,
              C.repr, 
              arb);
    assume arb != null;
    assume arb != x;
    assume arb != C.p[x];
    C.max := C.max[x := max];
    assert LC(C.k, C.prio, C.l, C.r, C.p, 
              C.min, C.max, C.keys,
              C.repr, 
              arb);
}

procedure Check_Set_keys(x: Ref, arb: Ref, keys: KeySet)
    modifies C.keys;
{
    assume x != null;
    assume LC(C.k, C.prio, C.l, C.r, C.p, 
              C.min, C.max, C.keys,
              C.repr, 
              arb);
    assume arb != null;
    assume arb != x;
    assume arb != C.p[x];
    C.keys := C.keys[x := keys];
    assert LC(C.k, C.prio, C.l, C.r, C.p, 
              C.min, C.max, C.keys,
              C.repr, 
              arb);
}

procedure Check_Set_repr(x: Ref, arb: Ref, repr: RefSet)
    modifies C.repr;
{
    assume x != null;
    assume LC(C.k, C.prio, C.l, C.r, C.p, 
              C.min, C.max, C.keys,
              C.repr, 
              arb);
    assume arb != null;
    assume arb != x;
    assume arb != C.p[x];
    C.repr := C.repr[x := repr];
    assert LC(C.k, C.prio, C.l, C.r, C.p, 
              C.min, C.max, C.keys,
              C.repr, 
              arb);
}
