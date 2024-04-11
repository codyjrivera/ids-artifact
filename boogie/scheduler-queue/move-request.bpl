// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions"
// by Adithya Murali, Cody Rivera, and P. Madhusudan.
// 
// Artifact by Cody Rivera, 2023-2024. 
//
// Remove the first item from a linked list, and also remove that
// item from the overlaid BST.

procedure ListRemoveFirstContract(q1s: Ref, q1t: Ref, x: Ref)
    returns (ret: Ref, node: Ref);
    requires RefSetsEqual(Br_bst, EmptyRefSet);
    requires RefSetsEqual(Br_list, EmptyRefSet);
    requires x != null ==> 
        LC(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
            C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
            C.next, C.prev, C.list_keys, C.list_repr, x);
    requires x != null ==> C.prev[x] == null;
    modifies Br_bst, Br_list, C.next, C.prev, C.list_keys, C.list_repr;
    ensures x == null ==> ret == null;
    ensures x != null ==> ret == old(C.next)[x];
    ensures node == x;
    ensures (ret != null ==>
                LC(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                    C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                    C.next, C.prev, C.list_keys, C.list_repr, x)
                && C.prev[ret] == null
                && RefSetsEqual(C.list_repr[ret], (old(C.list_repr)[x])[node := false])
                && KeySetsEqual(C.list_keys[ret], (old(C.list_keys)[x])[C.k[node] := false]));
    ensures (node != null ==>
                LC(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                    C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                    C.next, C.prev, C.list_keys, C.list_repr, x)
                && C.k[node] == old(C.k)[x]
                && C.next[node] == null
                && C.prev[node] == null);
    ensures RefSetsEqual(Br_bst, EmptyRefSet);
    ensures RefSetsEqual(Br_list, EmptyRefSet);
    // Framing conditions
    ensures Frame_all(
        C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
        C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
        C.next, C.prev, C.list_keys, C.list_repr,
        old(C.k), old(C.l), old(C.r), old(C.p), old(C.min), old(C.max), old(C.bst_size),
        old(C.bst_keys), old(C.bst_repr), old(C.bst_depth), old(C.bst_root),
        old(C.next), old(C.prev), old(C.list_keys), old(C.list_repr),
        if x == null then EmptyRefSet else old(C.list_repr)[x],
        old(alloc)
    );

procedure BSTDeleteInsideContract(q1s: Ref, q1t: Ref, root: Ref, x: Ref)
    returns (ret: Ref, node: Ref);
    requires root != null && x != null;
    requires RefSetsEqual(Br_bst, EmptyRefSet);
    requires RefSetsEqual(Br_list, EmptyRefSet);
    requires LC(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, x);
    requires C.p[x] != null;
    requires C.l[C.p[x]] == x || C.r[C.p[x]] == x;
    requires !(C.l[C.p[x]] == x && C.r[C.p[x]] == x);
    requires C.bst_root[x] == root;
    requires C.next[x] == null && C.prev[x] == null;
    requires q1s != null ==> x != q1s;
    modifies Br_bst, Br_list, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root;
    ensures node != null;
    ensures ret == null || ret == old(C.l)[x] || ret == old(C.r)[x];
    ensures (RefSetsEqual(old(C.bst_repr)[x], EmptyRefSet[x := true]) ==> ret == null);
    ensures ((RefSetSubset(EmptyRefSet[x := true], old(C.bst_repr)[x]) 
             && !RefSetsEqual(old(C.bst_repr)[x], EmptyRefSet[x := true]))
                ==> ret != null);
    ensures (ret != null ==>
                LC(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                    C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                    C.next, C.prev, C.list_keys, C.list_repr, ret)
                && KeySetsEqual(C.bst_keys[ret], (old(C.bst_keys)[x])[C.k[x] := false])
                && C.min[ret] >= old(C.min)[x]
                && C.max[ret] <= old(C.max)[x]
                && RefSetsEqual(C.bst_repr[ret], (old(C.bst_repr)[x])[x := false])
                && C.bst_root[ret] == root
                && C.p[ret] == old(C.p)[x]);
    ensures KeySetsEqual(C.bst_keys[root], (old(C.bst_keys)[root])[C.k[x] := false]);
    ensures C.min[root] == old(C.min)[root];
    ensures C.max[root] == old(C.max)[root];
    ensures RefSetsEqual(C.bst_repr[root], (old(C.bst_repr)[root])[x := false]);
    ensures C.bst_root[root] == old(C.bst_root)[root];
    ensures C.p[root] == old(C.p)[root];
    ensures node == x && C.k[node] == old(C.k)[x];
    ensures LC(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, node);
    ensures BST_Isolated(C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, node);
    ensures q1s != null ==> C.bst_root[q1s] == old(C.bst_root)[q1s];
    ensures RefSetsEqual(Br_bst, EmptyRefSet);
    ensures RefSetsEqual(Br_list, EmptyRefSet);
    // Framing conditions
    ensures Frame_all(
        C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
        C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
        C.next, C.prev, C.list_keys, C.list_repr,
        old(C.k), old(C.l), old(C.r), old(C.p), old(C.min), old(C.max), old(C.bst_size),
        old(C.bst_keys), old(C.bst_repr), old(C.bst_depth), old(C.bst_root),
        old(C.next), old(C.prev), old(C.list_keys), old(C.list_repr),
        old(C.bst_repr)[old(C.bst_root)[x]],
        old(alloc)
    );

procedure MoveRequest(q1s: Ref, q1t: Ref)
    returns (c: Ref, q1s': Ref, q1t': Ref)
    requires RefSetsEqual(Br_bst, EmptyRefSet);
    requires RefSetsEqual(Br_list, EmptyRefSet);
    requires Valid_Queue(
        C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
        C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
        C.next, C.prev, C.list_keys, C.list_repr,
        q1s, q1t
    );
    modifies Br_bst, Br_list, C.l, C.r, C.p, C.min, C.max, C.bst_size,
        C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
        C.next, C.prev, C.list_keys, C.list_repr;
    ensures RefSetsEqual(Br_bst, EmptyRefSet);
    ensures RefSetsEqual(Br_list, EmptyRefSet);
    ensures Valid_Queue(
        C.k, C.l, C.r, C.p, C.min, C.max, C.bst_size,
        C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
        C.next, C.prev, C.list_keys, C.list_repr,
        q1s', q1t'
    );
    ensures q1s == null ==> (
        q1s' == null
        && KeySetsEqual(C.bst_keys[q1t'], EmptyKeySet)
        && RefSetsEqual(C.bst_repr[q1t'], EmptyRefSet[q1t' := true])
    );
    ensures q1s != null ==> (
        (KeySetsEqual(old(C.list_keys)[q1s], EmptyKeySet[old(C.k)[q1s] := true]) 
            ==> q1s' == null)
        && ((KeySetSubset(EmptyKeySet[old(C.k)[q1s] := true], old(C.list_keys)[q1s])
          && !KeySetsEqual(old(C.list_keys)[q1s], EmptyKeySet[old(C.k)[q1s] := true]))
            ==> q1s' != null)
        && KeySetsEqual(C.bst_keys[q1t'], (old(C.bst_keys)[q1t])[old(C.k)[q1s] := false])
        && RefSetsEqual(C.bst_repr[q1t'], (old(C.bst_repr)[q1t])[q1s := false])
    );
    ensures q1s != null && q1s' != null ==> (
         KeySetsEqual(C.list_keys[q1s'], (old(C.list_keys)[q1s])[old(C.k)[q1s] := false])
         && RefSetsEqual(C.list_repr[q1s'], (old(C.list_repr)[q1s])[q1s := false])
    );
{
    var tmp: Ref;
    var c': Ref;
    var c_p: Ref;
    var q1t'_l: Ref;
    var q1t'_r: Ref;

    call InAllocParam(q1s);
    call InAllocParam(q1t);

    q1s' := q1s;
    q1t' := q1t;

    // First phase: remove list item.
    call q1s', c := ListRemoveFirstContract(q1s', q1t', q1s');

    if (c == null) {
        return;
    }

    // Second phase: remove c from the bst.
    call c_p := Get_p(c);
    call IfNotBr_ThenLC(c_p);
    call tmp, c' := BSTDeleteInsideContract(q1s', q1t', q1t', c);

    call IfNotBr_ThenLC(q1t');
    call q1t'_l := Get_l(q1t');
    call q1t'_r := Get_r(q1t');
    call IfNotBr_ThenLC(q1t'_l);
    call IfNotBr_ThenLC(q1t'_r);
    call IfNotBr_ThenLC(q1s');
}