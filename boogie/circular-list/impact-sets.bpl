// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions of Datastructures"
// by Anonymous Authors.
// 
// Artifact by Anonymous Author, 2023. 
//
// Impact set verification for circular lists.

procedure Check_Create(arb: Ref, k: int)
    modifies Br, alloc, C.k, C.next, C.prev, 
                C.last, C.len, C.rlen,
                C.keys, C.repr;
{
    var node: Ref;

    assume LC(C.k, C.next, C.prev, 
                C.last, C.len, C.rlen,
                C.keys, C.repr,
              arb);
    assume arb != null;
    call InAllocParam(arb);
    call node := Create(k);
    assert LC(C.k, C.next, C.prev, 
                C.last, C.len, C.rlen,
                C.keys, C.repr,
              arb);
}

procedure Check_Set_k(x: Ref, arb: Ref, k: int)
    modifies C.k;
{
    assume x != null;
    assume LC(C.k, C.next, C.prev, 
                C.last, C.len, C.rlen,
                C.keys, C.repr, arb);
    assume arb != null;
    assume arb != x;
    assume arb != C.prev[x];
    C.k := C.k[x := k];
    assert LC(C.k, C.next, C.prev,
              C.last, C.len, C.rlen,
              C.keys, C.repr,
              arb);
}

procedure Check_Set_next(x: Ref, arb: Ref, next: Ref)
    modifies C.next;
{
    assume x != null;
    assume LC(C.k, C.next, C.prev,
              C.last, C.len, C.rlen,
              C.keys, C.repr,
              arb);
    assume arb != null;
    assume arb != x;
    assume arb != C.next[x];
    C.next := C.next[x := next];
    assert LC(C.k, C.next, C.prev,
              C.last, C.len, C.rlen,
              C.keys, C.repr,
              arb);
}

procedure Check_Set_prev(x: Ref, arb: Ref, prev: Ref)
    modifies C.prev;
{
    assume x != null;
    assume LC(C.k, C.next, C.prev,
              C.last, C.len, C.rlen,
              C.keys, C.repr,
              arb);
    assume arb != null;
    assume arb != x;
    assume arb != C.prev[x];
    C.prev := C.prev[x := prev];
    assert LC(C.k, C.next, C.prev,
              C.last, C.len, C.rlen,
              C.keys, C.repr,
              arb);
}

procedure Check_Set_last(x: Ref, arb: Ref, last: Ref)
    modifies C.last;
{
    assume x != null;
    assume LC(C.k, C.next, C.prev,
              C.last, C.len, C.rlen,
              C.keys, C.repr,
              arb);
    assume arb != null;
    assume C.last[x] != x || (C.last[x] == x && C.repr[x] == EmptyRefSet[x := true]);
    assume arb != x;
    assume arb != C.prev[x];
    C.last := C.last[x := last];
    assert LC(C.k, C.next, C.prev,
              C.last, C.len, C.rlen,
              C.keys, C.repr,
              arb);
}

procedure Check_Set_len(x: Ref, arb: Ref, len: int)
    modifies C.len;
{
    assume x != null;
    assume LC(C.k, C.next, C.prev, 
                C.last, C.len, C.rlen,
                C.keys, C.repr, arb);
    assume arb != null;
    assume arb != x;
    assume arb != C.prev[x];
    C.len := C.len[x := len];
    assert LC(C.k, C.next, C.prev,
              C.last, C.len, C.rlen,
              C.keys, C.repr,
              arb);
}

procedure Check_Set_rlen(x: Ref, arb: Ref, rlen: int)
    modifies C.rlen;
{
    assume x != null;
    assume LC(C.k, C.next, C.prev, 
                C.last, C.len, C.rlen,
                C.keys, C.repr, arb);
    assume arb != null;
    assume arb != x;
    assume arb != C.next[x];
    C.rlen := C.rlen[x := rlen];
    assert LC(C.k, C.next, C.prev,
              C.last, C.len, C.rlen,
              C.keys, C.repr,
              arb);
}

procedure Check_Set_keys(x: Ref, arb: Ref, keys: KeySet)
    modifies C.keys;
{
    assume x != null;
    assume LC(C.k, C.next, C.prev,
              C.last, C.len, C.rlen,
              C.keys, C.repr,
              arb);
    assume arb != null;
    assume arb != x;
    assume arb != C.prev[x];
    C.keys := C.keys[x := keys];
    assert LC(C.k, C.next, C.prev,
              C.last, C.len, C.rlen,
              C.keys, C.repr,
              arb);
}

procedure Check_Set_repr(x: Ref, arb: Ref, repr: RefSet)
    modifies C.repr;
{
    assume x != null;
    assume LC(C.k, C.next, C.prev,
              C.last, C.len, C.rlen,
              C.keys, C.repr,
              arb);
    assume arb != null;
    assume C.last[x] != x || (C.last[x] == x && C.repr[x] == EmptyRefSet[x := true]);
    assume arb != x;
    assume arb != C.prev[x];
    C.repr := C.repr[x := repr];
    assert LC(C.k, C.next, C.prev,
              C.last, C.len, C.rlen,
              C.keys, C.repr,
              arb);
}

procedure Check_AddToLastRepr(x: Ref, arb: Ref, node: Ref)
    modifies C.repr;
{
    assume x != null;
    assume LC(C.k, C.next, C.prev,
              C.last, C.len, C.rlen,
              C.keys, C.repr,
              arb);
    assume arb != null;
    assume C.last[x] == x;
    assume arb != x;
    C.repr := C.repr[x := (C.repr[x])[node := true]];
    assert LC(C.k, C.next, C.prev,
              C.last, C.len, C.rlen,
              C.keys, C.repr,
              arb);
}

procedure Check_AddToLastKeys(x: Ref, arb: Ref, k: int)
    modifies C.keys;
{
    assume x != null;
    assume LC(C.k, C.next, C.prev,
              C.last, C.len, C.rlen,
              C.keys, C.repr,
              arb);
    assume arb != null;
    assume C.last[x] == x;
    assume arb != x;
    C.keys := C.keys[x := (C.keys[x])[k := true]];
    assert LC(C.k, C.next, C.prev,
              C.last, C.len, C.rlen,
              C.keys, C.repr,
              arb);
}

procedure Check_DeleteFromLastRepr(x: Ref, arb: Ref, node: Ref)
    modifies C.repr;
{
    assume x != null;
    assume LC(C.k, C.next, C.prev,
              C.last, C.len, C.rlen,
              C.keys, C.repr,
              arb);
    assume arb != null;
    assume C.last[x] == x && C.next[node] == node && C.prev[node] == node;
    assume arb != x;
    C.repr := C.repr[x := (C.repr[x])[node := false]];
    assert LC(C.k, C.next, C.prev,
              C.last, C.len, C.rlen,
              C.keys, C.repr,
              arb);
}

procedure Check_DeleteFromLastKeys(x: Ref, arb: Ref, k: int)
    modifies C.keys;
{
    assume x != null;
    assume LC(C.k, C.next, C.prev,
              C.last, C.len, C.rlen,
              C.keys, C.repr,
              arb);
    assume arb != null;
    assume C.last[x] == x;
    assume arb != x;
    C.keys := C.keys[x := (C.keys[x])[k := false]];
    assert LC(C.k, C.next, C.prev,
              C.last, C.len, C.rlen,
              C.keys, C.repr,
              arb);
}
