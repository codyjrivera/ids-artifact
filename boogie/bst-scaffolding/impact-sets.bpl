// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions"
// by Adithya Murali, Cody Rivera, and P. Madhusudan.
// 
// Artifact by Cody Rivera, 2023-2024. 
//
// Impact set verification for BSTs with scaffolding.

procedure Check_Create(arb: Ref, k: int)
    modifies Br, alloc, C.k, C.l, C.r, C.p, 
              C.min, C.max, C.size, C.keys,
              C.repr, C.depth, C.root;
{
    var node: Ref;

    assume LC(C.k, C.l, C.r, C.p, 
              C.min, C.max, C.size, C.keys,
              C.repr, C.depth, C.root,
              arb);
    assume arb != null;
    call InAllocParam(arb);
    call node := Create(k);
    assert LC(C.k, C.l, C.r, C.p, 
              C.min, C.max, C.size, C.keys,
              C.repr, C.depth, C.root,
              arb);
}

procedure Check_Set_k(x: Ref, arb: Ref, k: int)
    modifies C.k;
{
    assume x != null;
    assume LC(C.k, C.l, C.r, C.p, 
              C.min, C.max, C.size, C.keys,
              C.repr, C.depth, C.root, 
              arb);
    assume arb != null;
    assume arb != x;
    assume arb != C.p[x];
    C.k := C.k[x := k];
    assert LC(C.k, C.l, C.r, C.p, 
              C.min, C.max, C.size, C.keys,
              C.repr, C.depth, C.root, 
              arb);
}

procedure Check_Set_l(x: Ref, arb: Ref, l: Ref)
    modifies C.l;
{
    assume x != null;
    assume LC(C.k, C.l, C.r, C.p, 
              C.min, C.max, C.size, C.keys,
              C.repr, C.depth, C.root, 
              arb);
    assume arb != null;
    assume arb != x;
    assume arb != C.l[x];
    C.l := C.l[x := l];
    assert LC(C.k, C.l, C.r, C.p, 
              C.min, C.max, C.size, C.keys,
              C.repr, C.depth, C.root, 
              arb);
}

procedure Check_Set_r(x: Ref, arb: Ref, r: Ref)
    modifies C.r;
{
    assume x != null;
    assume LC(C.k, C.l, C.r, C.p, 
              C.min, C.max, C.size, C.keys,
              C.repr, C.depth, C.root, 
              arb);
    assume arb != null;
    assume arb != x;
    assume arb != C.r[x];
    C.r := C.r[x := r];
    assert LC(C.k, C.l, C.r, C.p, 
              C.min, C.max, C.size, C.keys,
              C.repr, C.depth, C.root, 
              arb);
}

procedure Check_Set_p(x: Ref, arb: Ref, p: Ref)
    modifies C.p;
{
    assume x != null;
    assume LC(C.k, C.l, C.r, C.p, 
              C.min, C.max, C.size, C.keys,
              C.repr, C.depth, C.root, 
              arb);
    assume arb != null;
    assume C.p[x] != null;
    assume arb != x;
    assume arb != C.p[x];
    C.p := C.p[x := p];
    assert LC(C.k, C.l, C.r, C.p, 
              C.min, C.max, C.size, C.keys,
              C.repr, C.depth, C.root, 
              arb);
}

procedure Check_Set_min(x: Ref, arb: Ref, min: int)
    modifies C.min;
{
    assume x != null;
    assume LC(C.k, C.l, C.r, C.p, 
              C.min, C.max, C.size, C.keys,
              C.repr, C.depth, C.root, 
              arb);
    assume arb != null;
    assume arb != x;
    assume arb != C.p[x];
    C.min := C.min[x := min];
    assert LC(C.k, C.l, C.r, C.p, 
              C.min, C.max, C.size, C.keys,
              C.repr, C.depth, C.root, 
              arb);
}

procedure Check_Set_max(x: Ref, arb: Ref, max: int)
    modifies C.max;
{
    assume x != null;
    assume LC(C.k, C.l, C.r, C.p, 
              C.min, C.max, C.size, C.keys,
              C.repr, C.depth, C.root, 
              arb);
    assume arb != null;
    assume arb != x;
    assume arb != C.p[x];
    C.max := C.max[x := max];
    assert LC(C.k, C.l, C.r, C.p, 
              C.min, C.max, C.size, C.keys,
              C.repr, C.depth, C.root, 
              arb);
}

procedure Check_Set_size(x: Ref, arb: Ref, size: int)
    modifies C.size;
{
    assume x != null;
    assume LC(C.k, C.l, C.r, C.p, 
              C.min, C.max, C.size, C.keys,
              C.repr, C.depth, C.root, 
              arb);
    assume arb != null;
    assume arb != x;
    assume arb != C.p[x];
    C.size := C.size[x := size];
    assert LC(C.k, C.l, C.r, C.p, 
              C.min, C.max, C.size, C.keys,
              C.repr, C.depth, C.root, 
              arb);
}

procedure Check_Set_keys(x: Ref, arb: Ref, keys: KeySet)
    modifies C.keys;
{
    assume x != null;
    assume LC(C.k, C.l, C.r, C.p, 
              C.min, C.max, C.size, C.keys,
              C.repr, C.depth, C.root, 
              arb);
    assume arb != null;
    assume arb != x;
    assume arb != C.p[x];
    C.keys := C.keys[x := keys];
    assert LC(C.k, C.l, C.r, C.p, 
              C.min, C.max, C.size, C.keys,
              C.repr, C.depth, C.root, 
              arb);
}

procedure Check_Set_repr(x: Ref, arb: Ref, repr: RefSet)
    modifies C.repr;
{
    assume x != null;
    assume LC(C.k, C.l, C.r, C.p, 
              C.min, C.max, C.size, C.keys,
              C.repr, C.depth, C.root, 
              arb);
    assume arb != null;
    assume C.p[x] != null;
    assume arb != x;
    assume arb != C.p[x];
    C.repr := C.repr[x := repr];
    assert LC(C.k, C.l, C.r, C.p, 
              C.min, C.max, C.size, C.keys,
              C.repr, C.depth, C.root, 
              arb);
}

procedure Check_Set_root(x: Ref, arb: Ref, root: Ref)
    modifies C.root;
{
    assume x != null;
    assume LC(C.k, C.l, C.r, C.p, 
              C.min, C.max, C.size, C.keys,
              C.repr, C.depth, C.root, 
              arb);
    assume arb != null;
    assume C.p[x] != null;
    assume arb != x;
    assume arb != C.l[x];
    assume arb != C.r[x];
    C.root := C.root[x := root];
    assert LC(C.k, C.l, C.r, C.p, 
              C.min, C.max, C.size, C.keys,
              C.repr, C.depth, C.root, 
              arb);
}

procedure Check_Set_depth(x: Ref, arb: Ref, depth: int)
    modifies C.depth;
{
    assume x != null;
    assume LC(C.k, C.l, C.r, C.p, 
              C.min, C.max, C.size, C.keys,
              C.repr, C.depth, C.root, 
              arb);
    assume arb != null;
    assume C.p[x] != null;
    assume arb != x;
    assume arb != C.l[x];
    assume arb != C.r[x];
    C.depth := C.depth[x := depth];
    assert LC(C.k, C.l, C.r, C.p, 
              C.min, C.max, C.size, C.keys,
              C.repr, C.depth, C.root, 
              arb);
}

procedure Check_DeleteFromRootRepr(x: Ref, arb: Ref, node: Ref)
    modifies C.repr;
{
    assume x != null;
    assume LC(C.k, C.l, C.r, C.p, 
              C.min, C.max, C.size, C.keys,
              C.repr, C.depth, C.root, 
              arb);
    assume arb != null;
    assume C.p[x] == null;
    assume Isolated(C.k, C.l, C.r, C.p, 
              C.min, C.max, C.size, C.keys,
              C.repr, C.depth, C.root, 
              node);
    assume arb != x;
    C.repr := C.repr[x := (C.repr[x])[node := false]];
    assert LC(C.k, C.l, C.r, C.p, 
              C.min, C.max, C.size, C.keys,
              C.repr, C.depth, C.root, 
              arb);
}
