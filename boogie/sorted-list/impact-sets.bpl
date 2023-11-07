// Supporting Artifact for
// "Predictive Verification using Intrinsic Definitions of Data Structures"
// by Adithya Murali, Cody Rivera, and P. Madhusudan.
// 
// Artifact by Cody Rivera, 2023. 
//
// Impact set verification for sorted lists.

//SETUP:num_paths=1; (number of paths in the program)

procedure Check_Set_k(x: Ref, arb: Ref, k: int)
    modifies C.k;
{
    assume x != null;
    assume LC(C.k, C.next, C.prev, C.keys, C.repr, C.sorted, C.rev_sorted, arb, alloc);
    assume arb != null;
    assume arb != x;
    assume arb != C.prev[x];
    C.k := C.k[x := k];
    assert LC(C.k, C.next, C.prev, C.keys, C.repr, C.sorted, C.rev_sorted, arb, alloc);
}

procedure Check_Set_next(x: Ref, arb: Ref, next: Ref)
    modifies C.next;
{
    assume x != null;
    assume LC(C.k, C.next, C.prev, C.keys, C.repr, C.sorted, C.rev_sorted, arb, alloc);
    assume arb != null;
    assume arb != x;
    assume arb != C.next[x];
    C.next := C.next[x := next];
    assert LC(C.k, C.next, C.prev, C.keys, C.repr, C.sorted, C.rev_sorted, arb, alloc);
}

procedure Check_Set_prev(x: Ref, arb: Ref, prev: Ref)
    modifies C.prev;
{
    assume x != null;
    assume LC(C.k, C.next, C.prev, C.keys, C.repr, C.sorted, C.rev_sorted, arb, alloc);
    assume arb != null;
    assume arb != x;
    assume arb != C.prev[x];
    C.prev := C.prev[x := prev];
    assert LC(C.k, C.next, C.prev, C.keys, C.repr, C.sorted, C.rev_sorted, arb, alloc);
}

procedure Check_Set_keys(x: Ref, arb: Ref, keys: KeySet)
    modifies C.keys;
{
    assume x != null;
    assume LC(C.k, C.next, C.prev, C.keys, C.repr, C.sorted, C.rev_sorted, arb, alloc);
    assume arb != null;
    assume arb != x;
    assume arb != C.prev[x];
    C.keys := C.keys[x := keys];
    assert LC(C.k, C.next, C.prev, C.keys, C.repr, C.sorted, C.rev_sorted, arb, alloc);
}

procedure Check_Set_repr(x: Ref, arb: Ref, repr: RefSet)
    modifies C.repr;
{
    assume x != null;
    assume LC(C.k, C.next, C.prev, C.keys, C.repr, C.sorted, C.rev_sorted, arb, alloc);
    assume arb != null;
    assume arb != x;
    assume arb != C.prev[x];
    C.repr := C.repr[x := repr];
    assert LC(C.k, C.next, C.prev, C.keys, C.repr, C.sorted, C.rev_sorted, arb, alloc);
}

procedure Check_Set_sorted(x: Ref, arb: Ref, sorted: bool)
    modifies C.sorted;
{
    assume x != null;
    assume LC(C.k, C.next, C.prev, C.keys, C.repr, C.sorted, C.rev_sorted, arb, alloc);
    assume arb != null;
    assume arb != x;
    assume arb != C.prev[x];
    C.sorted := C.sorted[x := sorted];
    assert LC(C.k, C.next, C.prev, C.keys, C.repr, C.sorted, C.rev_sorted, arb, alloc);
}

procedure Check_Set_rev_sorted(x: Ref, arb: Ref, rev_sorted: bool)
    modifies C.rev_sorted;
{
    assume x != null;
    assume LC(C.k, C.next, C.prev, C.keys, C.repr, C.sorted, C.rev_sorted, arb, alloc);
    assume arb != null;
    assume arb != x;
    assume arb != C.prev[x];
    C.rev_sorted := C.rev_sorted[x := rev_sorted];
    assert LC(C.k, C.next, C.prev, C.keys, C.repr, C.sorted, C.rev_sorted, arb, alloc);
}
