// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions"
// by Adithya Murali, Cody Rivera, and P. Madhusudan.
// 
// Artifact by Cody Rivera, 2023-2024. 
//
// Impact set verification for scheduler queue.

procedure Check_Create(arb1: Ref, arb2: Ref, k: int, prio: int)
    modifies Br_bst, Br_list, alloc, C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr;
{
    var node: Ref;

    assume LC_BST(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, arb1);
    assume LC_List(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, arb2);
    assume arb1 != null;
    assume arb2 != null;
    call InAllocParam(arb1);
    call InAllocParam(arb2);
    call node := Create(k);
    assert LC_BST(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, arb1);
    assert LC_List(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, arb2);
}

procedure Check_Set_k(x: Ref, arb1: Ref, arb2: Ref, k: int)
    modifies C.k;
{
    assume x != null;
    assume LC_BST(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, arb1);
    assume LC_List(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, arb2);
    assume arb1 != null;
    assume arb2 != null;
    assume arb1 != x;
    assume arb2 != x;
    C.k := C.k[x := k];
    assert LC_BST(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, arb1);
    assert LC_List(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, arb2);
}

procedure Check_Set_l(x: Ref, arb1: Ref, arb2: Ref, l: Ref)
    modifies C.l;
{
    assume x != null;
    assume LC_BST(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, arb1);
    assume LC_List(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, arb2);
    assume arb1 != null;
    assume arb2 != null;
    assume arb1 != C.l[x];
    assume arb1 != x;
    C.l := C.l[x := l];
    assert LC_BST(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, arb1);
    assert LC_List(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, arb2);
}

procedure Check_Set_r(x: Ref, arb1: Ref, arb2: Ref, r: Ref)
    modifies C.r;
{
    assume x != null;
    assume LC_BST(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, arb1);
    assume LC_List(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, arb2);
    assume arb1 != null;
    assume arb2 != null;
    assume arb1 != C.r[x];
    assume arb1 != x;
    C.r := C.r[x := r];
    assert LC_BST(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, arb1);
    assert LC_List(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, arb2);
}

procedure Check_Set_p(x: Ref, arb1: Ref, arb2: Ref, p: Ref)
    modifies C.p;
{
    assume x != null;
    assume LC_BST(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, arb1);
    assume LC_List(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, arb2);
    assume arb1 != null;
    assume arb2 != null;
    assume C.p[x] != null;
    assume arb1 != C.p[x];
    assume arb1 != x;
    C.p := C.p[x := p];
    assert LC_BST(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, arb1);
    assert LC_List(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, arb2);
}

procedure Check_Set_min(x: Ref, arb1: Ref, arb2: Ref, min: int)
    modifies C.min;
{
    assume x != null;
    assume LC_BST(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, arb1);
    assume LC_List(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, arb2);
    assume arb1 != null;
    assume arb2 != null;
    assume arb1 != C.p[x];
    assume arb1 != x;
    C.min := C.min[x := min];
    assert LC_BST(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, arb1);
    assert LC_List(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, arb2);
}

procedure Check_Set_max(x: Ref, arb1: Ref, arb2: Ref, max: int)
    modifies C.max;
{
    assume x != null;
    assume LC_BST(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, arb1);
    assume LC_List(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, arb2);
    assume arb1 != null;
    assume arb2 != null;
    assume arb1 != C.p[x];
    assume arb1 != x;
    C.max := C.max[x := max];
    assert LC_BST(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, arb1);
    assert LC_List(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, arb2);
}

procedure Check_Set_bst_keys(x: Ref, arb1: Ref, arb2: Ref, bst_keys: KeySet)
    modifies C.bst_keys;
{
    assume x != null;
    assume LC_BST(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, arb1);
    assume LC_List(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, arb2);
    assume arb1 != null;
    assume arb2 != null;
    assume arb1 != C.p[x];
    assume arb1 != x;
    C.bst_keys := C.bst_keys[x := bst_keys];
    assert LC_BST(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, arb1);
    assert LC_List(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, arb2);
}

procedure Check_Set_bst_repr(x: Ref, arb1: Ref, arb2: Ref, bst_repr: RefSet)
    modifies C.bst_repr;
{
    assume x != null;
    assume LC_BST(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, arb1);
    assume LC_List(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, arb2);
    assume arb1 != null;
    assume arb2 != null;
    assume C.p[x] != null;
    assume arb1 != C.p[x];
    assume arb1 != x;
    C.bst_repr := C.bst_repr[x := bst_repr];
    assert LC_BST(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, arb1);
    assert LC_List(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, arb2);
}

procedure Check_Set_bst_depth(x: Ref, arb1: Ref, arb2: Ref, bst_depth: int)
    modifies C.bst_depth;
{
    assume x != null;
    assume LC_BST(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, arb1);
    assume LC_List(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, arb2);
    assume arb1 != null;
    assume arb2 != null;
    assume arb1 != C.l[x];
    assume arb1 != C.r[x];
    assume arb1 != x;
    C.bst_depth := C.bst_depth[x := bst_depth];
    assert LC_BST(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, arb1);
    assert LC_List(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, arb2);
}

procedure Check_Set_bst_root(x: Ref, arb1: Ref, arb2: Ref, bst_root: Ref)
    modifies C.bst_root;
{
    assume x != null;
    assume LC_BST(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, arb1);
    assume LC_List(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, arb2);
    assume arb1 != null;
    assume arb2 != null;
    assume arb1 != x;
    assume arb1 != C.l[x];
    assume arb1 != C.r[x];
    assume arb2 != x;
    assume arb2 != C.prev[x];
    C.bst_root := C.bst_root[x := bst_root];
    assert LC_BST(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, arb1);
    assert LC_List(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, arb2);
}

procedure Check_DeleteFromRootRepr(x: Ref, arb1: Ref, arb2: Ref, node: Ref)
    modifies C.bst_repr;
{
    assume x != null;
    assume LC_BST(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, arb1);
    assume LC_List(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, arb2);
    assume arb1 != null;
    assume arb2 != null;
    assume BST_Isolated(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                        C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                        C.next, C.prev, C.list_keys, C.list_repr, node);
    assume C.p[x] == null;
    assume arb1 != x;
    C.bst_repr := C.bst_repr[x := (C.bst_repr[x])[node := false]];
    assert LC_BST(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, arb1);
    assert LC_List(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, arb2);
}

procedure Check_Set_next(x: Ref, arb1: Ref, arb2: Ref, next: Ref)
    modifies C.next;
{
    assume x != null;
    assume LC_BST(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, arb1);
    assume LC_List(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, arb2);
    assume arb1 != null;
    assume arb2 != null;
    assume arb2 != C.next[x];
    assume arb2 != x;
    C.next := C.next[x := next];
    assert LC_BST(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, arb1);
    assert LC_List(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, arb2);
}

procedure Check_Set_prev(x: Ref, arb1: Ref, arb2: Ref, prev: Ref)
    modifies C.prev;
{
    assume x != null;
    assume LC_BST(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, arb1);
    assume LC_List(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, arb2);
    assume arb1 != null;
    assume arb2 != null;
    assume arb2 != C.prev[x];
    assume arb2 != x;
    C.prev := C.prev[x := prev];
    assert LC_BST(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, arb1);
    assert LC_List(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, arb2);
}

procedure Check_Set_list_keys(x: Ref, arb1: Ref, arb2: Ref, list_keys: KeySet)
    modifies C.list_keys;
{
    assume x != null;
    assume LC_BST(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, arb1);
    assume LC_List(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, arb2);
    assume arb1 != null;
    assume arb2 != null;
    assume arb2 != C.prev[x];
    assume arb2 != x;
    C.list_keys := C.list_keys[x := list_keys];
    assert LC_BST(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, arb1);
    assert LC_List(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, arb2);
}

procedure Check_Set_list_repr(x: Ref, arb1: Ref, arb2: Ref, list_repr: RefSet)
    modifies C.list_repr;
{
    assume x != null;
    assume LC_BST(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, arb1);
    assume LC_List(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, arb2);
    assume arb1 != null;
    assume arb2 != null;
    assume arb2 != C.prev[x];
    assume arb2 != x;
    C.list_repr := C.list_repr[x := list_repr];
    assert LC_BST(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, arb1);
    assert LC_List(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, arb2);
}
