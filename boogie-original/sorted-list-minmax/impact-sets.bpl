// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions"
// by Adithya Murali, Cody Rivera, and P. Madhusudan.
// 
// Artifact by Cody Rivera, 2023. 
//
// Impact set verification for sorted lists (with min/max).

procedure Check_Create(arb: Ref, k: int)
    modifies Br, alloc, C.k, C.next, C.prev,
              C.keys, C.repr,
              C.sorted, C.rev_sorted, C.min, C.max;
{
    var node: Ref;

    assume LC(C.k, C.next, C.prev,
              C.keys, C.repr,
              C.sorted, C.rev_sorted, C.min, C.max,
              arb);
    assume arb != null;
    call InAllocParam(arb);
    call node := Create(k);
    assert LC(C.k, C.next, C.prev,
              C.keys, C.repr,
              C.sorted, C.rev_sorted, C.min, C.max,
              arb);
}

procedure Check_Set_k(x: Ref, arb: Ref, k: int)
    modifies C.k;
{
    assume x != null;
    assume LC(C.k, C.next, C.prev,
              C.keys, C.repr,
              C.sorted, C.rev_sorted, C.min, C.max,
              arb);
    assume arb != null;
    assume arb != x;
    assume arb != C.prev[x];
    C.k := C.k[x := k];
    assert LC(C.k, C.next, C.prev,
              C.keys, C.repr,
              C.sorted, C.rev_sorted, C.min, C.max,
              arb);
}

procedure Check_Set_next(x: Ref, arb: Ref, next: Ref)
    modifies C.next;
{
    assume x != null;
    assume LC(C.k, C.next, C.prev,
              C.keys, C.repr,
              C.sorted, C.rev_sorted, C.min, C.max,
              arb);
    assume arb != null;
    assume arb != x;
    assume arb != C.next[x];
    C.next := C.next[x := next];
    assert LC(C.k, C.next, C.prev,
              C.keys, C.repr,
              C.sorted, C.rev_sorted, C.min, C.max,
              arb);
}

procedure Check_Set_prev(x: Ref, arb: Ref, prev: Ref)
    modifies C.prev;
{
    assume x != null;
    assume LC(C.k, C.next, C.prev,
              C.keys, C.repr,
              C.sorted, C.rev_sorted, C.min, C.max,
              arb);
    assume arb != null;
    assume arb != x;
    assume arb != C.prev[x];
    C.prev := C.prev[x := prev];
    assert LC(C.k, C.next, C.prev,
              C.keys, C.repr,
              C.sorted, C.rev_sorted, C.min, C.max,
              arb);
}

procedure Check_Set_min(x: Ref, arb: Ref, min: int)
    modifies C.min;
{
    assume x != null;
    assume LC(C.k, C.next, C.prev,
              C.keys, C.repr,
              C.sorted, C.rev_sorted, C.min, C.max,
              arb);
    assume arb != null;
    assume arb != x;
    assume arb != C.prev[x];
    C.min := C.min[x := min];
    assert LC(C.k, C.next, C.prev,
              C.keys, C.repr,
              C.sorted, C.rev_sorted, C.min, C.max,
              arb);
}

procedure Check_Set_max(x: Ref, arb: Ref, max: int)
    modifies C.max;
{
    assume x != null;
    assume LC(C.k, C.next, C.prev,
              C.keys, C.repr,
              C.sorted, C.rev_sorted, C.min, C.max,
              arb);
    assume arb != null;
    assume arb != x;
    assume arb != C.prev[x];
    C.max := C.max[x := max];
    assert LC(C.k, C.next, C.prev,
              C.keys, C.repr,
              C.sorted, C.rev_sorted, C.min, C.max,
              arb);
}

procedure Check_Set_keys(x: Ref, arb: Ref, keys: KeySet)
    modifies C.keys;
{
    assume x != null;
    assume LC(C.k, C.next, C.prev,
              C.keys, C.repr,
              C.sorted, C.rev_sorted, C.min, C.max,
              arb);
    assume arb != null;
    assume arb != x;
    assume arb != C.prev[x];
    C.keys := C.keys[x := keys];
    assert LC(C.k, C.next, C.prev,
              C.keys, C.repr,
              C.sorted, C.rev_sorted, C.min, C.max,
              arb);
}

procedure Check_Set_repr(x: Ref, arb: Ref, repr: RefSet)
    modifies C.repr;
{
    assume x != null;
    assume LC(C.k, C.next, C.prev,
              C.keys, C.repr,
              C.sorted, C.rev_sorted, C.min, C.max,
              arb);
    assume arb != null;
    assume arb != x;
    assume arb != C.prev[x];
    C.repr := C.repr[x := repr];
    assert LC(C.k, C.next, C.prev,
              C.keys, C.repr,
              C.sorted, C.rev_sorted, C.min, C.max,
              arb);
}
