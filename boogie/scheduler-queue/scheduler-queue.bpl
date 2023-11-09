// Supporting Artifact for
// "Predictive Verification using Intrinsic Definitions of Data Structures"
// by Adithya Murali, Cody Rivera, and P. Madhusudan.
// 
// Artifact by Cody Rivera, 2023. 
//
// Definition of Scheduler Queue (overlay of BST and list).

// Datatype aliases
type Ref;
const null: Ref;

type KeySet = [int]bool;
type RefSet = [Ref]bool;

// Set library
const EmptyKeySet: KeySet;
function KeySetMember(x: int, s2: KeySet) returns (bool);
function KeySetAddF(s: KeySet, x: int) returns (KeySet);
function KeySetRemoveF(s: KeySet, x: int) returns (KeySet);
function KeySetIntersectF(s1: KeySet, s2: KeySet) returns (KeySet);
function KeySetUnionF(s1: KeySet, s2: KeySet) returns (KeySet);
function KeySetComF(s: KeySet) returns (KeySet);
function KeySetDiffF(s1: KeySet, s2: KeySet) returns (KeySet);
function KeySetSubset(s1: KeySet, s2: KeySet) returns (bool);
function KeySetsEqual(s1: KeySet, s2: KeySet) returns (bool);
function KeySetsDisjoint(s1: KeySet, s2: KeySet) returns (bool);

const EmptyRefSet: RefSet;
function RefSetMember(x: Ref, s2: RefSet) returns (bool);
function RefSetAddF(s: RefSet, x: Ref) returns (RefSet);
function RefSetRemoveF(s: RefSet, x: Ref) returns (RefSet);
function RefSetIntersectF(s1: RefSet, s2: RefSet) returns (RefSet);
function RefSetUnionF(s1: RefSet, s2: RefSet) returns (RefSet);
function RefSetComF(s: RefSet) returns (RefSet);
function RefSetDiffF(s1: RefSet, s2: RefSet) returns (RefSet);
function RefSetSubset(s1: RefSet, s2: RefSet) returns (bool);
function RefSetsEqual(s1: RefSet, s2: RefSet) returns (bool);
function RefSetsDisjoint(s1: RefSet, s2: RefSet) returns (bool);

// Fields
var C.k: [Ref]int;

// BST fields
var C.l: [Ref]Ref;
var C.r: [Ref]Ref;
var C.p: [Ref]Ref;
var C.min: [Ref]int;
var C.max: [Ref]int;
var C.bst_keys: [Ref]KeySet;
var C.bst_repr: [Ref]RefSet;
var C.bst_depth: [Ref]int;
var C.bst_root: [Ref]Ref;

// List fields
var C.next: [Ref]Ref;
var C.prev: [Ref]Ref;
var C.list_keys: [Ref]KeySet;
var C.list_repr: [Ref]RefSet;

var Br_bst: RefSet;
var Br_list: RefSet;
var alloc: RefSet;

// Local conditions
function {:inline} LC(
    k: [Ref]int, 
    l: [Ref]Ref,
    r: [Ref]Ref,
    p: [Ref]Ref,
    min: [Ref]int,
    max: [Ref]int,
    bst_keys: [Ref]KeySet,
    bst_repr: [Ref]RefSet,
    bst_depth: [Ref]int,
    bst_root: [Ref]Ref,
    next: [Ref]Ref,
    prev: [Ref]Ref,
    list_keys: [Ref]KeySet,
    list_repr: [Ref]RefSet,
    x: Ref
) returns (bool)
{
    LC_BST(
        k, 
        l,
        r,
        p,
        min,
        max,
        bst_keys,
        bst_repr,
        bst_depth,
        bst_root,
        next,
        prev,
        list_keys,
        list_repr,
        x
    )
    &&
    LC_List(
        k, 
        l,
        r,
        p,
        min,
        max,
        bst_keys,
        bst_repr,
        bst_depth,
        bst_root,
        next,
        prev,
        list_keys,
        list_repr,
        x
    )
}

function {:inline} LC_BST(
    k: [Ref]int, 
    l: [Ref]Ref,
    r: [Ref]Ref,
    p: [Ref]Ref,
    min: [Ref]int,
    max: [Ref]int,
    bst_keys: [Ref]KeySet,
    bst_repr: [Ref]RefSet,
    bst_depth: [Ref]int,
    bst_root: [Ref]Ref,
    next: [Ref]Ref,
    prev: [Ref]Ref,
    list_keys: [Ref]KeySet,
    list_repr: [Ref]RefSet,
    x: Ref
) returns (bool)
{
    x != null ==> (
        (x == bst_root[x] ==> 
            (bst_repr[x])[x]
            && p[x] == null
            && bst_depth[x] == 0
            && l[x] == null
            && (r[x] == null ==>
                    RefSetsEqual(bst_repr[x], EmptyRefSet[x := true])
                    && KeySetsEqual(bst_keys[x], EmptyKeySet))
            && (r[x] != null ==>
                    p[r[x]] == x
                    && RefSetsEqual(bst_repr[x], (bst_repr[r[x]])[x := true])
                    && !(bst_repr[r[x]])[x]
                    && KeySetsEqual(bst_keys[x], bst_keys[r[x]])))
        && (x != bst_root[x] ==>
                (bst_repr[x])[x]
                && min[x] <= k[x]
                && k[x] <= max[x]
                && p[x] != null
                && !(bst_repr[x])[p[x]]
                && (l[p[x]] == x || r[p[x]] == x)
                && !(bst_repr[x])[bst_root[x]]
                && bst_depth[x] == bst_depth[p[x]] + 1
                && (l[x] != null ==> 
                        (bst_repr[x])[l[x]]
                        && !(bst_repr[l[x]])[x]
                        && p[l[x]] == x
                        && max[l[x]] < k[x])
                && (r[x] != null ==> 
                        (bst_repr[x])[r[x]]
                        && !(bst_repr[r[x]])[x]
                        && p[r[x]] == x
                        && min[r[x]] > k[x])
                && (l[x] == null && r[x] == null ==>
                        RefSetsEqual(bst_repr[x], EmptyRefSet[x := true])
                        && KeySetsEqual(bst_keys[x], EmptyKeySet[k[x] := true])
                        && min[x] == k[x] 
                        && k[x] == max[x]
                        )
                && (l[x] != null && r[x] == null ==>
                        RefSetsEqual(bst_repr[x], (bst_repr[l[x]])[x := true])
                        && KeySetsEqual(bst_keys[x], (bst_keys[l[x]])[k[x] := true])
                        && !(bst_keys[l[x]])[k[x]]
                        && min[x] == min[l[x]] && max[x] == k[x]
                        )
                && (l[x] == null && r[x] != null ==>
                        RefSetsEqual(bst_repr[x], (bst_repr[r[x]])[x := true])
                        && KeySetsEqual(bst_keys[x], (bst_keys[r[x]])[k[x] := true])
                        && !(bst_keys[r[x]])[k[x]]
                        && min[x] == k[x] && max[x] == max[r[x]]
                        )
                && (l[x] != null && r[x] != null ==>
                        RefSetsEqual(bst_repr[x], RefSetUnionF((bst_repr[l[x]])[x := true], bst_repr[r[x]]))
                        && RefSetsDisjoint(bst_repr[l[x]], bst_repr[r[x]])
                        && KeySetsEqual(bst_keys[x], KeySetUnionF((bst_keys[l[x]])[k[x] := true], bst_keys[r[x]]))
                        && KeySetsDisjoint(bst_keys[l[x]], bst_keys[r[x]])
                        && !(bst_keys[l[x]])[k[x]] && !(bst_keys[r[x]])[k[x]]
                        && min[x] == min[l[x]] && max[x] == max[r[x]]
                        )
                && bst_root[x] == bst_root[p[x]]
                && (bst_repr[bst_root[x]])[x]
                && (bst_repr[bst_root[x]])[p[x]]
                && (l[x] != null ==> (bst_repr[bst_root[x]])[l[x]])
                && (r[x] != null ==> (bst_repr[bst_root[x]])[r[x]])
                && p[bst_root[x]] == null)
        && bst_depth[x] >= 0
        && bst_root[x] != null
    )
}

function {:inline} LC_List(
    k: [Ref]int, 
    l: [Ref]Ref,
    r: [Ref]Ref,
    p: [Ref]Ref,
    min: [Ref]int,
    max: [Ref]int,
    bst_keys: [Ref]KeySet,
    bst_repr: [Ref]RefSet,
    bst_depth: [Ref]int,
    bst_root: [Ref]Ref,
    next: [Ref]Ref,
    prev: [Ref]Ref,
    list_keys: [Ref]KeySet,
    list_repr: [Ref]RefSet,
    x: Ref
) returns (bool)
{
    x != null ==> (
        (list_repr[x])[x]
        && (prev[x] != null ==>
                !(list_repr[x])[prev[x]]
                && next[prev[x]] == x)
        && (next[x] == null ==>
                RefSetsEqual(list_repr[x], EmptyRefSet[x := true])
                && KeySetsEqual(list_keys[x], EmptyKeySet[k[x] := true]))
        && (next[x] != null ==>
                (list_repr[x])[next[x]]
                && RefSetsEqual(list_repr[x], (list_repr[next[x]])[x := true])
                && !(list_repr[next[x]])[x]
                && KeySetsEqual(list_keys[x], (list_keys[next[x]])[k[x] := true])
                && !(list_keys[next[x]])[k[x]]
                && prev[next[x]] == x
                && bst_root[x] == bst_root[next[x]])
        && bst_root[x] != null
    )
}

function {:inline} LC_Trans_NoDepth(
    k: [Ref]int, 
    l: [Ref]Ref,
    r: [Ref]Ref,
    p: [Ref]Ref,
    min: [Ref]int,
    max: [Ref]int,
    bst_keys: [Ref]KeySet,
    bst_repr: [Ref]RefSet,
    bst_depth: [Ref]int,
    bst_root: [Ref]Ref,
    next: [Ref]Ref,
    prev: [Ref]Ref,
    list_keys: [Ref]KeySet,
    list_repr: [Ref]RefSet,
    x: Ref
) returns (bool)
{
    LC_BST_Trans_NoDepth(
        k, 
        l,
        r,
        p,
        min,
        max,
        bst_keys,
        bst_repr,
        bst_depth,
        bst_root,
        next,
        prev,
        list_keys,
        list_repr,
        x
    )
    &&
    LC_List(
        k, 
        l,
        r,
        p,
        min,
        max,
        bst_keys,
        bst_repr,
        bst_depth,
        bst_root,
        next,
        prev,
        list_keys,
        list_repr,
        x
    )
}

function {:inline} LC_BST_Trans_NoDepth(
    k: [Ref]int, 
    l: [Ref]Ref,
    r: [Ref]Ref,
    p: [Ref]Ref,
    min: [Ref]int,
    max: [Ref]int,
    bst_keys: [Ref]KeySet,
    bst_repr: [Ref]RefSet,
    bst_depth: [Ref]int,
    bst_root: [Ref]Ref,
    next: [Ref]Ref,
    prev: [Ref]Ref,
    list_keys: [Ref]KeySet,
    list_repr: [Ref]RefSet,
    x: Ref
) returns (bool)
{
    x != null ==> (
        (x == bst_root[x] ==> 
            (bst_repr[x])[x]
            && p[x] == null
            //&& bst_depth[x] == 0
            && l[x] == null
            && (r[x] == null ==>
                    RefSetsEqual(bst_repr[x], EmptyRefSet[x := true])
                    && KeySetsEqual(bst_keys[x], EmptyKeySet))
            && (r[x] != null ==>
                    p[r[x]] == x
                    && RefSetsEqual(bst_repr[x], (bst_repr[r[x]])[x := true])
                    && !(bst_repr[r[x]])[x]
                    && KeySetsEqual(bst_keys[x], bst_keys[r[x]])))
        && (x != bst_root[x] ==>
                (bst_repr[x])[x]
                && min[x] <= k[x]
                && k[x] <= max[x]
                && p[x] != null
                && !(bst_repr[x])[p[x]]
                && (l[p[x]] == x || r[p[x]] == x)
                && !(bst_repr[x])[bst_root[x]]
                //&& bst_depth[x] == bst_depth[p[x]] + 1
                && (l[x] != null ==> 
                        (bst_repr[x])[l[x]]
                        && !(bst_repr[l[x]])[x]
                        && p[l[x]] == x
                        && max[l[x]] < k[x])
                && (r[x] != null ==> 
                        (bst_repr[x])[r[x]]
                        && !(bst_repr[r[x]])[x]
                        && p[r[x]] == x
                        && min[r[x]] > k[x])
                && (l[x] == null && r[x] == null ==>
                        RefSetsEqual(bst_repr[x], EmptyRefSet[x := true])
                        && KeySetsEqual(bst_keys[x], EmptyKeySet[k[x] := true])
                        && min[x] == k[x] 
                        && k[x] == max[x]
                        )
                && (l[x] != null && r[x] == null ==>
                        RefSetsEqual(bst_repr[x], (bst_repr[l[x]])[x := true])
                        && KeySetsEqual(bst_keys[x], (bst_keys[l[x]])[k[x] := true])
                        && !(bst_keys[l[x]])[k[x]]
                        && min[x] == min[l[x]] && max[x] == k[x]
                        )
                && (l[x] == null && r[x] != null ==>
                        RefSetsEqual(bst_repr[x], (bst_repr[r[x]])[x := true])
                        && KeySetsEqual(bst_keys[x], (bst_keys[r[x]])[k[x] := true])
                        && !(bst_keys[r[x]])[k[x]]
                        && min[x] == k[x] && max[x] == max[r[x]]
                        )
                && (l[x] != null && r[x] != null ==>
                        RefSetsEqual(bst_repr[x], RefSetUnionF((bst_repr[l[x]])[x := true], bst_repr[r[x]]))
                        && RefSetsDisjoint(bst_repr[l[x]], bst_repr[r[x]])
                        && KeySetsEqual(bst_keys[x], KeySetUnionF((bst_keys[l[x]])[k[x] := true], bst_keys[r[x]]))
                        && KeySetsDisjoint(bst_keys[l[x]], bst_keys[r[x]])
                        && !(bst_keys[l[x]])[k[x]] && !(bst_keys[r[x]])[k[x]]
                        && min[x] == min[l[x]] && max[x] == max[r[x]]
                        )
                && bst_root[x] == bst_root[p[x]]
                && (bst_repr[bst_root[x]])[x]
                && (bst_repr[bst_root[x]])[p[x]]
                && (l[x] != null ==> (bst_repr[bst_root[x]])[l[x]])
                && (r[x] != null ==> (bst_repr[bst_root[x]])[r[x]])
                && p[bst_root[x]] == null)
        && bst_depth[x] >= 0
        && bst_root[x] != null
    )
}

function {:inline} LC_Trans_PlusNode(
    k: [Ref]int, 
    l: [Ref]Ref,
    r: [Ref]Ref,
    p: [Ref]Ref,
    min: [Ref]int,
    max: [Ref]int,
    bst_keys: [Ref]KeySet,
    bst_repr: [Ref]RefSet,
    bst_depth: [Ref]int,
    bst_root: [Ref]Ref,
    next: [Ref]Ref,
    prev: [Ref]Ref,
    list_keys: [Ref]KeySet,
    list_repr: [Ref]RefSet,
    x: Ref,
    node: Ref
) returns (bool)
{
    LC_BST_Trans_PlusNode(
        k, 
        l,
        r,
        p,
        min,
        max,
        bst_keys,
        bst_repr,
        bst_depth,
        bst_root,
        next,
        prev,
        list_keys,
        list_repr,
        x,
        node
    )
    &&
    LC_List(
        k, 
        l,
        r,
        p,
        min,
        max,
        bst_keys,
        bst_repr,
        bst_depth,
        bst_root,
        next,
        prev,
        list_keys,
        list_repr,
        x
    )
}

function {:inline} LC_BST_Trans_PlusNode(
    k: [Ref]int, 
    l: [Ref]Ref,
    r: [Ref]Ref,
    p: [Ref]Ref,
    min: [Ref]int,
    max: [Ref]int,
    bst_keys: [Ref]KeySet,
    bst_repr: [Ref]RefSet,
    bst_depth: [Ref]int,
    bst_root: [Ref]Ref,
    next: [Ref]Ref,
    prev: [Ref]Ref,
    list_keys: [Ref]KeySet,
    list_repr: [Ref]RefSet,
    x: Ref,
    node: Ref
) returns (bool)
{
    (x != null && node != null) ==> (
        (x == bst_root[x] ==> 
            (bst_repr[x])[x]
            && p[x] == null
            && bst_depth[x] == 0
            && l[x] == null
            && (r[x] == null ==>
                    RefSetsEqual(bst_repr[x], (EmptyRefSet[x := true])[node := true])
                    && KeySetsEqual(bst_keys[x], EmptyKeySet[k[node] := true]))
            && (r[x] != null ==>
                    p[r[x]] == x
                    && RefSetsEqual(bst_repr[x], ((bst_repr[r[x]])[x := true])[node := true])
                    && !(bst_repr[r[x]])[x]
                    && KeySetsEqual(bst_keys[x], (bst_keys[r[x]])[k[node] := true])))
        && (x != bst_root[x] ==>
                (bst_repr[x])[x]
                && min[x] <= k[x]
                && k[x] <= max[x]
                && p[x] != null
                && !(bst_repr[x])[p[x]]
                && (l[p[x]] == x || r[p[x]] == x)
                && !(bst_repr[x])[bst_root[x]]
                && bst_depth[x] == bst_depth[p[x]] + 1
                && (l[x] != null ==> 
                        (bst_repr[x])[l[x]]
                        && !(bst_repr[l[x]])[x]
                        && p[l[x]] == x
                        && max[l[x]] < k[x])
                && (r[x] != null ==> 
                        (bst_repr[x])[r[x]]
                        && !(bst_repr[r[x]])[x]
                        && p[r[x]] == x
                        && min[r[x]] > k[x])
                && (l[x] == null && r[x] == null ==>
                        RefSetsEqual(bst_repr[x], (EmptyRefSet[x := true])[node := true])
                        && KeySetsEqual(bst_keys[x], (EmptyKeySet[k[x] := true])[k[node] := true])
                        //&& min[x] == k[x] 
                        //&& k[x] == max[x]
                        )
                && (l[x] != null && r[x] == null ==>
                        RefSetsEqual(bst_repr[x], ((bst_repr[l[x]])[x := true])[node := true])
                        && KeySetsEqual(bst_keys[x], ((bst_keys[l[x]])[k[x] := true])[k[node] := true])
                        && !(bst_keys[l[x]])[k[x]]
                        //&& min[x] == min[l[x]] && max[x] == k[x]
                        )
                && (l[x] == null && r[x] != null ==>
                        RefSetsEqual(bst_repr[x], ((bst_repr[r[x]])[x := true])[node := true])
                        && KeySetsEqual(bst_keys[x], ((bst_keys[r[x]])[k[x] := true])[k[node] := true])
                        && !(bst_keys[r[x]])[k[x]]
                        //&& min[x] == k[x] && max[x] == max[r[x]]
                        )
                && (l[x] != null && r[x] != null ==>
                        RefSetsEqual(bst_repr[x], (RefSetUnionF((bst_repr[l[x]])[x := true], bst_repr[r[x]]))[node := true])
                        && RefSetsDisjoint(bst_repr[l[x]], bst_repr[r[x]])
                        && KeySetsEqual(bst_keys[x], (KeySetUnionF((bst_keys[l[x]])[k[x] := true], bst_keys[r[x]]))[k[node] := true])
                        && KeySetsDisjoint(bst_keys[l[x]], bst_keys[r[x]])
                        && !(bst_keys[l[x]])[k[x]] && !(bst_keys[r[x]])[k[x]]
                        //&& min[x] == min[l[x]] && max[x] == max[r[x]]
                        )
                && bst_root[x] == bst_root[p[x]]
                && (bst_repr[bst_root[x]])[x]
                && (bst_repr[bst_root[x]])[p[x]]
                && (l[x] != null ==> (bst_repr[bst_root[x]])[l[x]])
                && (r[x] != null ==> (bst_repr[bst_root[x]])[r[x]])
                && p[bst_root[x]] == null)
            && bst_depth[x] >= 0
            && bst_root[x] != null
        )
}

// Queue validity.
function {:inline} Valid_Queue(
    k: [Ref]int, 
    l: [Ref]Ref,
    r: [Ref]Ref,
    p: [Ref]Ref,
    min: [Ref]int,
    max: [Ref]int,
    bst_keys: [Ref]KeySet,
    bst_repr: [Ref]RefSet,
    bst_depth: [Ref]int,
    bst_root: [Ref]Ref,
    next: [Ref]Ref,
    prev: [Ref]Ref,
    list_keys: [Ref]KeySet,
    list_repr: [Ref]RefSet,
    q1s: Ref,
    q1t: Ref
) returns (bool)
{
    q1t != null
    && p[q1t] == null
    && LC(k, l, r, p, min, max,
            bst_keys, bst_repr, bst_depth, bst_root,
            next, prev, list_keys, list_repr, q1t)
    && (q1s != null <==> (l[q1t] == null && r[q1t] == null))
    && (q1s != null ==>
            LC(k, l, r, p, min, max,
                bst_keys, bst_repr, bst_depth, bst_root,
                next, prev, list_keys, list_repr, q1s)
            && prev[q1s] == null
            && bst_root[q1s] == q1t
            && RefSetsEqual(list_repr[q1s], (bst_repr[q1t])[q1t := false])
            && KeySetsEqual(list_keys[q1s], bst_keys[q1t]))
}

// Accessor Macros.
procedure Get_k(x: Ref) returns (k: int);
    requires x != null;
    ensures k == C.k[x];

procedure Get_l(x: Ref) returns (l: Ref);
    requires x != null;
    ensures l == C.l[x];
    ensures InAlloc(C.k, C.l, C.r, C.p, C.min, C.max,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, l, alloc);

procedure Get_r(x: Ref) returns (r: Ref);
    requires x != null;
    ensures r == C.r[x];
    ensures InAlloc(C.k, C.l, C.r, C.p, C.min, C.max,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, r, alloc);

procedure Get_p(x: Ref) returns (p: Ref);
    requires x != null;
    ensures p == C.p[x];
    ensures InAlloc(C.k, C.l, C.r, C.p, C.min, C.max,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, p, alloc);

procedure Get_min(x: Ref) returns (min: int);
    requires x != null;
    ensures min == C.min[x];

procedure Get_max(x: Ref) returns (max: int);
    requires x != null;
    ensures max == C.max[x];

procedure Get_bst_keys(x: Ref) returns (bst_keys: KeySet);
    requires x != null;
    ensures bst_keys == C.bst_keys[x];

procedure Get_bst_repr(x: Ref) returns (bst_repr: RefSet);
    requires x != null;
    ensures bst_repr == C.bst_repr[x];
    ensures RefSetSubset(bst_repr, alloc);

procedure Get_bst_depth(x: Ref) returns (bst_depth: int);
    requires x != null;
    ensures bst_depth == C.bst_depth[x];

procedure Get_bst_root(x: Ref) returns (bst_root: Ref);
    requires x != null;
    ensures bst_root == C.bst_root[x];
    ensures InAlloc(C.k, C.l, C.r, C.p, C.min, C.max,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, bst_root, alloc);

procedure Get_next(x: Ref) returns (next: Ref);
    requires x != null;
    ensures next == C.next[x];
    ensures InAlloc(C.k, C.l, C.r, C.p, C.min, C.max,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, next, alloc);

procedure Get_prev(x: Ref) returns (prev: Ref);
    requires x != null;
    ensures prev == C.prev[x];
    ensures InAlloc(C.k, C.l, C.r, C.p, C.min, C.max,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, prev, alloc);

procedure Get_list_keys(x: Ref) returns (list_keys: KeySet);
    requires x != null;
    ensures list_keys == C.list_keys[x];

procedure Get_list_repr(x: Ref) returns (list_repr: RefSet);
    requires x != null;
    ensures list_repr == C.list_repr[x];
    ensures RefSetSubset(list_repr, alloc);

// Manipulation macros
procedure Create(k: int) returns (node: Ref);
    modifies Br_bst, Br_list, alloc, C.k, C.l, C.r, C.p, C.next, C.prev, C.bst_root;
    ensures node != null;
    ensures !old(alloc)[node];
    ensures alloc == old(alloc)[node := true];
    ensures C.k == old(C.k)[node := k];
    ensures C.l == old(C.l)[node := null];
    ensures C.r == old(C.r)[node := null];
    ensures C.p == old(C.p)[node := node];
    ensures C.next == old(C.next)[node := null];
    ensures C.prev == old(C.prev)[node := null];
    ensures C.bst_root == old(C.bst_root)[node := node];
    ensures Br_bst == old(Br_bst)[node := true];
    ensures Br_list == old(Br_list)[node := true];

procedure Set_k(x: Ref, k: int);
    requires x != null;
    modifies Br_bst, C.k;
    ensures C.k == old(C.k)[x := k];
    ensures C.p[x] != null ==> Br_bst == (old(Br_bst)[x := true])[C.p[x] := true];
    ensures C.p[x] == null ==> Br_bst == old(Br_bst)[x := true];

procedure Set_l(x: Ref, l: Ref);
    requires x != null;
    modifies Br_bst, C.l;
    ensures C.l == old(C.l)[x := l];
    ensures old(C.l)[x] != null ==> Br_bst == (old(Br_bst)[x := true])[old(C.l)[x] := true];
    ensures old(C.l)[x] == null ==> Br_bst == old(Br_bst)[x := true];

procedure Set_r(x: Ref, r: Ref);
    requires x != null;
    modifies Br_bst, C.r;
    ensures C.r == old(C.r)[x := r];
    ensures old(C.r)[x] != null ==> Br_bst == (old(Br_bst)[x := true])[old(C.r)[x] := true];
    ensures old(C.r)[x] == null ==> Br_bst == old(Br_bst)[x := true];

procedure Set_p(x: Ref, p: Ref);
    requires x != null;
    requires C.p[x] != null;
    modifies Br_bst, C.p;
    ensures C.p == old(C.p)[x := p];
    ensures old(C.p)[x] != null ==> Br_bst == (old(Br_bst)[x := true])[old(C.p)[x] := true];
    ensures old(C.p)[x] == null ==> Br_bst == old(Br_bst)[x := true];

procedure Set_min(x: Ref, min: int);
    requires x != null;
    modifies Br_bst, C.min;
    ensures C.min == old(C.min)[x := min];
    ensures C.p[x] != null ==> Br_bst == (old(Br_bst)[x := true])[C.p[x] := true];
    ensures C.p[x] == null ==> Br_bst == old(Br_bst)[x := true];

procedure Set_max(x: Ref, max: int);
    requires x != null;
    modifies Br_bst, C.max;
    ensures C.max == old(C.max)[x := max];
    ensures C.p[x] != null ==> Br_bst == (old(Br_bst)[x := true])[C.p[x] := true];
    ensures C.p[x] == null ==> Br_bst == old(Br_bst)[x := true];

procedure Set_bst_keys(x: Ref, bst_keys: KeySet);
    requires x != null;
    modifies Br_bst, C.bst_keys;
    ensures C.bst_keys == old(C.bst_keys)[x := bst_keys];
    ensures C.p[x] != null ==> Br_bst == (old(Br_bst)[x := true])[C.p[x] := true];
    ensures C.p[x] == null ==> Br_bst == old(Br_bst)[x := true];

procedure Set_bst_repr(x: Ref, bst_repr: RefSet);
    requires x != null;
    requires C.p[x] != null;
    modifies Br_bst, C.bst_repr;
    ensures C.bst_repr == old(C.bst_repr)[x := bst_repr];
    ensures C.p[x] != null ==> Br_bst == (old(Br_bst)[x := true])[C.p[x] := true];
    ensures C.p[x] == null ==> Br_bst == old(Br_bst)[x := true];

procedure Set_bst_depth(x: Ref, bst_depth: int);
    requires x != null;
    modifies Br_bst, C.bst_depth;
    ensures C.bst_depth == old(C.bst_depth)[x := bst_depth];
    ensures Br_bst == if C.l[x] == null then
                        if C.r[x] == null then
                            old(Br_bst)[x := true]
                        else
                            (old(Br_bst)[x := true])[C.r[x] := true]
                      else
                        if C.r[x] == null then
                            (old(Br_bst)[x := true])[C.l[x] := true]
                        else
                            ((old(Br_bst)[x := true])[C.l[x] := true])[C.r[x] := true];

procedure Set_bst_root(x: Ref, bst_root: Ref);
    requires x != null;
    modifies Br_bst, Br_list, C.bst_root;
    ensures C.bst_root == old(C.bst_root)[x := bst_root];
    ensures Br_bst == if C.l[x] == null then
                        if C.r[x] == null then
                            old(Br_bst)[x := true]
                        else
                            (old(Br_bst)[x := true])[C.r[x] := true]
                      else
                        if C.r[x] == null then
                            (old(Br_bst)[x := true])[C.l[x] := true]
                        else
                            ((old(Br_bst)[x := true])[C.l[x] := true])[C.r[x] := true];
    ensures C.prev[x] != null ==> Br_list == (old(Br_list)[x := true])[C.prev[x] := true];
    ensures C.prev[x] == null ==> Br_list == old(Br_list)[x := true];

procedure DeleteFromRootRepr(x: Ref, node: Ref);
    requires x != null;
    modifies Br_bst, C.bst_repr;
    ensures C.bst_repr == old(C.bst_repr)[x := (old(C.bst_repr)[x])[node := false]];
    ensures Br_bst == old(Br_bst)[x := true];

procedure Set_next(x: Ref, next: Ref);
    requires x != null;
    modifies Br_list, C.next;
    ensures C.next == old(C.next)[x := next];
    ensures old(C.next)[x] != null ==> Br_list == (old(Br_list)[x := true])[old(C.next)[x] := true];
    ensures old(C.next)[x] == null ==> Br_list == old(Br_list)[x := true];

procedure Set_prev(x: Ref, prev: Ref);
    requires x != null;
    modifies Br_list, C.prev;
    ensures C.prev == old(C.prev)[x := prev];
    ensures old(C.prev)[x] != null ==> Br_list == (old(Br_list)[x := true])[old(C.prev)[x] := true];
    ensures old(C.prev)[x] == null ==> Br_list == old(Br_list)[x := true];

procedure Set_list_keys(x: Ref, list_keys: KeySet);
    requires x != null;
    modifies Br_list, C.list_keys;
    ensures C.list_keys == old(C.list_keys)[x := list_keys];
    ensures C.prev[x] != null ==> Br_list == (old(Br_list)[x := true])[C.prev[x] := true];
    ensures C.prev[x] == null ==> Br_list == old(Br_list)[x := true];

procedure Set_list_repr(x: Ref, list_repr: RefSet);
    requires x != null;
    modifies Br_list, C.list_repr;
    ensures C.list_repr == old(C.list_repr)[x := list_repr];
    ensures C.prev[x] != null ==> Br_list == (old(Br_list)[x := true])[C.prev[x] := true];
    ensures C.prev[x] == null ==> Br_list == old(Br_list)[x := true];

// Broken set manipulation
procedure IfNotBr_ThenLC(x: Ref);
    ensures (x != null && !Br_list[x] && !Br_bst[x]) ==> 
            LC(C.k, C.l, C.r, C.p, C.min, C.max,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, x);

procedure IfNotBrList_ThenListLC(x: Ref);
    ensures (x != null && !Br_list[x]) ==> 
            LC_List(C.k, C.l, C.r, C.p, C.min, C.max,
                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                C.next, C.prev, C.list_keys, C.list_repr, x);

procedure AssertLCAndRemove(x: Ref);
    modifies Br_list, Br_bst;
    ensures (x != null && LC(C.k, C.l, C.r, C.p, C.min, C.max,
                                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                                C.next, C.prev, C.list_keys, C.list_repr, x)) 
                ==> (Br_list == old(Br_list)[x := false]
                    && Br_bst == old(Br_bst)[x := false]);
    ensures (x == null || !LC(C.k, C.l, C.r, C.p, C.min, C.max,
                            C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                            C.next, C.prev, C.list_keys, C.list_repr, x))
                ==> (Br_list == old(Br_list)
                    && Br_bst == old(Br_bst));

// Framing
function Frame_k(mod_set: RefSet, old_k: [Ref]int, k: [Ref]int) returns ([Ref]int);
function Frame_l(mod_set: RefSet, old_l: [Ref]Ref, l: [Ref]Ref) returns ([Ref]Ref);
function Frame_r(mod_set: RefSet, old_r: [Ref]Ref, r: [Ref]Ref) returns ([Ref]Ref);
function Frame_p(mod_set: RefSet, old_p: [Ref]Ref, p: [Ref]Ref) returns ([Ref]Ref);
function Frame_min(mod_set: RefSet, old_min: [Ref]int, min: [Ref]int) returns ([Ref]int);
function Frame_max(mod_set: RefSet, old_max: [Ref]int, max: [Ref]int) returns ([Ref]int);
function Frame_bst_keys(mod_set: RefSet, old_bst_keys: [Ref]KeySet, bst_keys: [Ref]KeySet) returns ([Ref]KeySet);
function Frame_bst_repr(mod_set: RefSet, old_bst_repr: [Ref]RefSet, bst_repr: [Ref]RefSet) returns ([Ref]RefSet);
function Frame_bst_depth(mod_set: RefSet, old_bst_depth: [Ref]int, bst_depth: [Ref]int) returns ([Ref]int);
function Frame_bst_root(mod_set: RefSet, old_bst_root: [Ref]Ref, bst_root: [Ref]Ref) returns ([Ref]Ref);
function Frame_next(mod_set: RefSet, old_next: [Ref]Ref, next: [Ref]Ref) returns ([Ref]Ref);
function Frame_prev(mod_set: RefSet, old_prev: [Ref]Ref, prev: [Ref]Ref) returns ([Ref]Ref);
function Frame_list_keys(mod_set: RefSet, old_list_keys: [Ref]KeySet, list_keys: [Ref]KeySet) returns ([Ref]KeySet);
function Frame_list_repr(mod_set: RefSet, old_list_repr: [Ref]RefSet, list_repr: [Ref]RefSet) returns ([Ref]RefSet);

function {:inline} Frame_all(
    k: [Ref]int, 
    l: [Ref]Ref,
    r: [Ref]Ref,
    p: [Ref]Ref,
    min: [Ref]int,
    max: [Ref]int,
    bst_keys: [Ref]KeySet,
    bst_repr: [Ref]RefSet,
    bst_depth: [Ref]int,
    bst_root: [Ref]Ref,
    next: [Ref]Ref,
    prev: [Ref]Ref,
    list_keys: [Ref]KeySet,
    list_repr: [Ref]RefSet,
    oldk: [Ref]int, 
    oldl: [Ref]Ref,
    oldr: [Ref]Ref,
    oldp: [Ref]Ref,
    oldmin: [Ref]int,
    oldmax: [Ref]int,
    oldbst_keys: [Ref]KeySet,
    oldbst_repr: [Ref]RefSet,
    oldbst_depth: [Ref]int,
    oldbst_root: [Ref]Ref,
    oldnext: [Ref]Ref,
    oldprev: [Ref]Ref,
    oldlist_keys: [Ref]KeySet,
    oldlist_repr: [Ref]RefSet,
    mod_set: RefSet,
    old_alloc: RefSet
) returns (bool) 
{
    k == Frame_k(RefSetUnionF(mod_set, RefSetComF(old_alloc)), oldk, k) 
    && l == Frame_l(RefSetUnionF(mod_set, RefSetComF(old_alloc)), oldl, l) 
    && r == Frame_r(RefSetUnionF(mod_set, RefSetComF(old_alloc)), oldr, r) 
    && p == Frame_p(RefSetUnionF(mod_set, RefSetComF(old_alloc)), oldp, p) 
    && min == Frame_min(RefSetUnionF(mod_set, RefSetComF(old_alloc)), oldmin, min) 
    && max == Frame_max(RefSetUnionF(mod_set, RefSetComF(old_alloc)), oldmax, max) 
    && bst_keys == Frame_bst_keys(RefSetUnionF(mod_set, RefSetComF(old_alloc)), oldbst_keys, bst_keys)
    && bst_repr == Frame_bst_repr(RefSetUnionF(mod_set, RefSetComF(old_alloc)), oldbst_repr, bst_repr)
    && bst_depth == Frame_bst_depth(RefSetUnionF(mod_set, RefSetComF(old_alloc)), oldbst_depth, bst_depth)
    && bst_root == Frame_bst_root(RefSetUnionF(mod_set, RefSetComF(old_alloc)), oldbst_root, bst_root)
    && next == Frame_next(RefSetUnionF(mod_set, RefSetComF(old_alloc)), oldnext, next)
    && prev == Frame_prev(RefSetUnionF(mod_set, RefSetComF(old_alloc)), oldprev, prev)
    && list_keys == Frame_list_keys(RefSetUnionF(mod_set, RefSetComF(old_alloc)), oldlist_keys, list_keys)
    && list_repr == Frame_list_repr(RefSetUnionF(mod_set, RefSetComF(old_alloc)), oldlist_repr, list_repr)
}

// Alloc set reasoning
function {:inline} InAlloc(
    k: [Ref]int, 
    l: [Ref]Ref,
    r: [Ref]Ref,
    p: [Ref]Ref,
    min: [Ref]int,
    max: [Ref]int,
    bst_keys: [Ref]KeySet,
    bst_repr: [Ref]RefSet,
    bst_depth: [Ref]int,
    bst_root: [Ref]Ref,
    next: [Ref]Ref,
    prev: [Ref]Ref,
    list_keys: [Ref]KeySet,
    list_repr: [Ref]RefSet,
    x: Ref,
    alloc: RefSet
) returns (bool)
{
    x != null ==> (
        alloc[x]
        && (l[x] != null ==> alloc[l[x]])
        && (r[x] != null ==> alloc[r[x]])
        && (p[x] != null ==> alloc[p[x]])
        && RefSetSubset(bst_repr[x], alloc)
        && (bst_root[x] != null ==> alloc[bst_root[x]])
        && (next[x] != null ==> alloc[next[x]])
        && (prev[x] != null ==> alloc[prev[x]])
        && RefSetSubset(list_repr[x], alloc)
    )
}

procedure InAllocParam(x: Ref);
    ensures x != null ==> InAlloc(C.k, C.l, C.r, C.p, C.min, C.max,
                                C.bst_keys, C.bst_repr, C.bst_depth, C.bst_root,
                                C.next, C.prev, C.list_keys, C.list_repr, 
                                x, alloc);

function {:inline} Fresh(expr: RefSet, newalloc: RefSet, oldalloc: RefSet) returns (bool)
{
    RefSetSubset(expr, newalloc)
    && RefSetsDisjoint(expr, oldalloc)
}

// Auxiliary functions
function {:inline} BST_Isolated(
    k: [Ref]int, 
    l: [Ref]Ref,
    r: [Ref]Ref,
    p: [Ref]Ref,
    min: [Ref]int,
    max: [Ref]int,
    bst_keys: [Ref]KeySet,
    bst_repr: [Ref]RefSet,
    bst_depth: [Ref]int,
    bst_root: [Ref]Ref,
    next: [Ref]Ref,
    prev: [Ref]Ref,
    list_keys: [Ref]KeySet,
    list_repr: [Ref]RefSet,
    x: Ref
) returns (bool)
{
  x != null ==> (
    p[x] == null && l[x] == null && r[x] == null
  )
}

function {:inline} BST_FieldsUnchanged(
    k: [Ref]int, 
    l: [Ref]Ref,
    r: [Ref]Ref,
    p: [Ref]Ref,
    min: [Ref]int,
    max: [Ref]int,
    bst_keys: [Ref]KeySet,
    bst_repr: [Ref]RefSet,
    bst_depth: [Ref]int,
    bst_root: [Ref]Ref,
    next: [Ref]Ref,
    prev: [Ref]Ref,
    list_keys: [Ref]KeySet,
    list_repr: [Ref]RefSet,
    oldk: [Ref]int, 
    oldl: [Ref]Ref,
    oldr: [Ref]Ref,
    oldp: [Ref]Ref,
    oldmin: [Ref]int,
    oldmax: [Ref]int,
    oldbst_keys: [Ref]KeySet,
    oldbst_repr: [Ref]RefSet,
    oldbst_depth: [Ref]int,
    oldbst_root: [Ref]Ref,
    oldnext: [Ref]Ref,
    oldprev: [Ref]Ref,
    oldlist_keys: [Ref]KeySet,
    oldlist_repr: [Ref]RefSet,
    x: Ref
) returns (bool)
{
  x != null ==> (
    l[x] == oldl[x]
    && r[x] == oldr[x]
    && p[x] == oldp[x]
    && min[x] == oldmin[x]
    && max[x] == oldmax[x]
    && bst_keys[x] == oldbst_keys[x]
    && bst_repr[x] == oldbst_repr[x]
    && bst_depth[x] == oldbst_depth[x]
    && bst_root[x] == oldbst_root[x]
  )
}

function {:inline} List_FieldsUnchanged(
    k: [Ref]int, 
    l: [Ref]Ref,
    r: [Ref]Ref,
    p: [Ref]Ref,
    min: [Ref]int,
    max: [Ref]int,
    bst_keys: [Ref]KeySet,
    bst_repr: [Ref]RefSet,
    bst_depth: [Ref]int,
    bst_root: [Ref]Ref,
    next: [Ref]Ref,
    prev: [Ref]Ref,
    list_keys: [Ref]KeySet,
    list_repr: [Ref]RefSet,
    oldk: [Ref]int, 
    oldl: [Ref]Ref,
    oldr: [Ref]Ref,
    oldp: [Ref]Ref,
    oldmin: [Ref]int,
    oldmax: [Ref]int,
    oldbst_keys: [Ref]KeySet,
    oldbst_repr: [Ref]RefSet,
    oldbst_depth: [Ref]int,
    oldbst_root: [Ref]Ref,
    oldnext: [Ref]Ref,
    oldprev: [Ref]Ref,
    oldlist_keys: [Ref]KeySet,
    oldlist_repr: [Ref]RefSet,
    x: Ref
) returns (bool)
{
  x != null ==> (
    next[x] == oldnext[x]
    && prev[x] == oldprev[x]
    && list_keys[x] == oldlist_keys[x]
    && list_repr[x] == oldlist_repr[x]
  )
}

function {:inline} FieldsUnchangedMinus_bst_depth(
    k: [Ref]int, 
    l: [Ref]Ref,
    r: [Ref]Ref,
    p: [Ref]Ref,
    min: [Ref]int,
    max: [Ref]int,
    bst_keys: [Ref]KeySet,
    bst_repr: [Ref]RefSet,
    bst_depth: [Ref]int,
    bst_root: [Ref]Ref,
    next: [Ref]Ref,
    prev: [Ref]Ref,
    list_keys: [Ref]KeySet,
    list_repr: [Ref]RefSet,
    oldk: [Ref]int, 
    oldl: [Ref]Ref,
    oldr: [Ref]Ref,
    oldp: [Ref]Ref,
    oldmin: [Ref]int,
    oldmax: [Ref]int,
    oldbst_keys: [Ref]KeySet,
    oldbst_repr: [Ref]RefSet,
    oldbst_depth: [Ref]int,
    oldbst_root: [Ref]Ref,
    oldnext: [Ref]Ref,
    oldprev: [Ref]Ref,
    oldlist_keys: [Ref]KeySet,
    oldlist_repr: [Ref]RefSet,
    x: Ref
) returns (bool)
{
  x != null ==> (
    l[x] == oldl[x]
    && r[x] == oldr[x]
    && p[x] == oldp[x]
    && min[x] == oldmin[x]
    && max[x] == oldmax[x]
    && bst_keys[x] == oldbst_keys[x]
    && bst_repr[x] == oldbst_repr[x]
    //&& bst_depth[x] == oldbst_depth[x]
    && bst_root[x] == oldbst_root[x]
    && next[x] == oldnext[x]
    && prev[x] == oldprev[x]
    && list_keys[x] == oldlist_keys[x]
    && list_repr[x] == oldlist_repr[x]
  )
}
