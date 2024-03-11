// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions"
// by Anonymous Authors.
// 
// Artifact by Anonymous Author, 2023. 
//
// Definition of Binary Search Trees.

// Datatype aliases
type Ref;
const null: Ref;

type KeySet = [int]bool;
type RefSet = [Ref]bool;

// Builtin parametric map updates
function {:builtin "MapConst"} MapConst_int_int(int) : [int]int;
function {:builtin "MapConst"} MapConst_int_bool(bool) : [int]bool;
function {:builtin "MapConst"} MapConst_Ref_int(int) : [Ref]int;
function {:builtin "MapConst"} MapConst_Ref_bool(bool) : [Ref]bool;
function {:builtin "MapAnd"} MapAnd_int_bool([int]bool, [int]bool) : [int]bool;
function {:builtin "MapOr"} MapOr_int_bool([int]bool, [int]bool) : [int]bool;
function {:builtin "MapNot"} MapNot_int_bool([int]bool) : [int]bool;
function {:builtin "MapAnd"} MapAnd_Ref_bool([Ref]bool, [Ref]bool) : [Ref]bool;
function {:builtin "MapOr"} MapOr_Ref_bool([Ref]bool, [Ref]bool) : [Ref]bool;
function {:builtin "MapNot"} MapNot_Ref_bool([Ref]bool) : [Ref]bool;
function {:builtin "MapIte"} MapIte_Ref_int([Ref]bool, [Ref]int, [Ref]int) : [Ref]int;
function {:builtin "MapIte"} MapIte_Ref_Ref([Ref]bool, [Ref]Ref, [Ref]Ref) : [Ref]Ref;
function {:builtin "MapIte"} MapIte_Ref_bool([Ref]bool, [Ref]bool, [Ref]bool) : [Ref]bool;
function {:builtin "MapIte"} MapIte_Ref_KeySet([Ref]bool, [Ref]KeySet, [Ref]KeySet) : [Ref]KeySet;
function {:builtin "MapIte"} MapIte_Ref_RefSet([Ref]bool, [Ref]RefSet, [Ref]RefSet) : [Ref]RefSet;

// Set library
const EmptyKeySet: KeySet;
axiom EmptyKeySet == MapConst_int_bool(false);

function {:inline} KeySetsEqual(s1: KeySet, s2: KeySet) returns (bool)
{
    s1 == s2 // WARNING: (==) symbol doesn't guarantee extensionality of equality.
             // (though it does in current versions of Boogie).
}

function {:inline} KeySetMember(x: int, s2: KeySet) returns (bool)
{
    s2[x]
}

function {:inline} KeySetAddF(s: KeySet, x: int) returns (KeySet)
{
    s[x := true]
}

function {:inline} KeySetRemoveF(s: KeySet, x: int) returns (KeySet)
{
    s[x := false]
}

function {:inline} KeySetIntersectF(s1: KeySet, s2: KeySet) returns (KeySet)
{
    MapAnd_int_bool(s1, s2)
}

function {:inline} KeySetUnionF(s1: KeySet, s2: KeySet) returns (KeySet)
{
    MapOr_int_bool(s1, s2)
}

function {:inline} KeySetComF(s: KeySet) returns (KeySet)
{
    MapNot_int_bool(s)
}

function {:inline} KeySetDiffF(s1: KeySet, s2: KeySet) returns (KeySet)
{
    KeySetIntersectF(s1, KeySetComF(s2))
}

function {:inline} KeySetSubset(s1: KeySet, s2: KeySet) returns (bool)
{
    KeySetsEqual(EmptyKeySet, KeySetDiffF(s1, s2))
}

function {:inline} KeySetsDisjoint(s1: KeySet, s2: KeySet) returns (bool)
{
    KeySetsEqual(EmptyKeySet, KeySetIntersectF(s1, s2))
}

const EmptyRefSet: RefSet;
axiom EmptyRefSet == MapConst_Ref_bool(false);

function {:inline} RefSetsEqual(s1: RefSet, s2: RefSet) returns (bool)
{
    s1 == s2 // WARNING: (==) symbol doesn't guarantee extensionality of equality.
             // (though it does in current versions of Boogie).
}

function {:inline} RefSetMember(x: Ref, s2: RefSet) returns (bool)
{
    s2[x]
}

function {:inline} RefSetAddF(s: RefSet, x: Ref) returns (RefSet)
{
    s[x := true]
}

function {:inline} RefSetRemoveF(s: RefSet, x: Ref) returns (RefSet)
{
    s[x := false]
}

function {:inline} RefSetIntersectF(s1: RefSet, s2: RefSet) returns (RefSet)
{
    MapAnd_Ref_bool(s1, s2)
}

function {:inline} RefSetUnionF(s1: RefSet, s2: RefSet) returns (RefSet)
{
    MapOr_Ref_bool(s1, s2)
}

function {:inline} RefSetComF(s: RefSet) returns (RefSet)
{
    MapNot_Ref_bool(s)
}

function {:inline} RefSetDiffF(s1: RefSet, s2: RefSet) returns (RefSet)
{
    RefSetIntersectF(s1, RefSetComF(s2))
}

function {:inline} RefSetSubset(s1: RefSet, s2: RefSet) returns (bool)
{
    RefSetsEqual(EmptyRefSet, RefSetDiffF(s1, s2))
}

function {:inline} RefSetsDisjoint(s1: RefSet, s2: RefSet) returns (bool)
{
    RefSetsEqual(EmptyRefSet, RefSetIntersectF(s1, s2))
}

// Fields
var C.k: [Ref]int;
var C.l: [Ref]Ref;
var C.r: [Ref]Ref;
var C.p: [Ref]Ref; // ghost
var C.min: [Ref]int; // ghost
var C.max: [Ref]int; // ghost
var C.keys: [Ref]KeySet; // ghost
var C.repr: [Ref]RefSet; // ghost

var Br: RefSet;
var alloc: RefSet;

// Local conditions
function {:inline} LC(
    k: [Ref]int,
    l: [Ref]Ref,
    r: [Ref]Ref,
    p: [Ref]Ref,
    min: [Ref]int,
    max: [Ref]int,
    keys: [Ref]KeySet,
    repr: [Ref]RefSet,
    x: Ref
) returns (bool)
{
    (x != null ==> (
        (repr[x])[x]
        && min[x] <= k[x] 
        && k[x] <= max[x]
        && (p[x] != null ==>
                !(repr[x])[p[x]]
                && (l[p[x]] == x || r[p[x]] == x))
        && (l[x] != null ==> 
                (repr[x])[l[x]]
                && !(repr[l[x]])[x]
                && p[l[x]] == x
                && max[l[x]] < k[x])
        && (r[x] != null ==> 
                (repr[x])[r[x]]
                && !(repr[r[x]])[x]
                && p[r[x]] == x
                && min[r[x]] > k[x])
        && (l[x] == null && r[x] == null ==>
                RefSetsEqual(repr[x], EmptyRefSet[x := true])
                && KeySetsEqual(keys[x], EmptyKeySet[k[x] := true])
                && min[x] == k[x] 
                && k[x] == max[x]
                )
        && (l[x] != null && r[x] == null ==>
                RefSetsEqual(repr[x], (repr[l[x]])[x := true])
                && KeySetsEqual(keys[x], (keys[l[x]])[k[x] := true])
                && !(keys[l[x]])[k[x]]
                && min[x] == min[l[x]] && max[x] == k[x]
                )
        && (l[x] == null && r[x] != null ==>
                RefSetsEqual(repr[x], (repr[r[x]])[x := true])
                && KeySetsEqual(keys[x], (keys[r[x]])[k[x] := true])
                && !(keys[r[x]])[k[x]]
                && min[x] == k[x] && max[x] == max[r[x]]
                )
        && (l[x] != null && r[x] != null ==>
                RefSetsEqual(repr[x], RefSetUnionF((repr[l[x]])[x := true], repr[r[x]]))
                && RefSetsDisjoint(repr[l[x]], repr[r[x]])
                && KeySetsEqual(keys[x], KeySetUnionF((keys[l[x]])[k[x] := true], keys[r[x]]))
                && KeySetsDisjoint(keys[l[x]], keys[r[x]])
                && !(keys[l[x]])[k[x]] && !(keys[r[x]])[k[x]]
                && min[x] == min[l[x]] && max[x] == max[r[x]]
                )
    ))
}

// Accessor Macros.
procedure Get_k(x: Ref) returns (k: int);
    requires x != null;
    ensures k == C.k[x];

procedure Get_l(x: Ref) returns (l: Ref);
    requires x != null;
    ensures l == C.l[x];
    ensures InAlloc(C.k, C.l, C.r, C.p, 
                C.min, C.max, C.keys, C.repr, 
                l, alloc);

procedure Get_r(x: Ref) returns (r: Ref);
    requires x != null;
    ensures r == C.r[x];
    ensures InAlloc(C.k, C.l, C.r, C.p, 
                C.min, C.max, C.keys, C.repr, 
                r, alloc);

procedure Get_p(x: Ref) returns (p: Ref);
    requires x != null;
    ensures p == C.p[x];
    ensures InAlloc(C.k, C.l, C.r, C.p, 
                C.min, C.max, C.keys, C.repr, 
                p, alloc);

procedure Get_min(x: Ref) returns (min: int);
    requires x != null;
    ensures min == C.min[x];

procedure Get_max(x: Ref) returns (max: int);
    requires x != null;
    ensures max == C.max[x];

procedure Get_keys(x: Ref) returns (keys: KeySet);
    requires x != null;
    ensures keys == C.keys[x];

procedure Get_repr(x: Ref) returns (repr: RefSet);
    requires x != null;
    ensures repr == C.repr[x];
    ensures RefSetSubset(repr, alloc);

// Manipulation macros
procedure Create(k: int) returns (node: Ref);
    modifies Br, alloc, C.k, C.l, C.r, C.p;
    ensures node != null;
    ensures !old(alloc)[node];
    ensures alloc == old(alloc)[node := true];
    ensures C.k == old(C.k)[node := k];
    ensures C.l == old(C.l)[node := null];
    ensures C.r == old(C.r)[node := null];
    ensures C.p == old(C.p)[node := null];
    ensures Br == old(Br)[node := true];

procedure Set_k(x: Ref, k: int);
    requires x != null;
    modifies Br, C.k;
    ensures C.k == old(C.k)[x := k];
    ensures C.p[x] != null ==> Br == (old(Br)[x := true])[C.p[x] := true];
    ensures C.p[x] == null ==> Br == old(Br)[x := true];

procedure Set_l(x: Ref, l: Ref);
    requires x != null;
    modifies Br, C.l;
    ensures C.l == old(C.l)[x := l];
    ensures old(C.l)[x] != null ==> Br == (old(Br)[x := true])[old(C.l)[x] := true];
    ensures old(C.l)[x] == null ==> Br == old(Br)[x := true];

procedure Set_r(x: Ref, r: Ref);
    requires x != null;
    modifies Br, C.r;
    ensures C.r == old(C.r)[x := r];
    ensures old(C.r)[x] != null ==> Br == (old(Br)[x := true])[old(C.r)[x] := true];
    ensures old(C.r)[x] == null ==> Br == old(Br)[x := true];

procedure Set_p(x: Ref, p: Ref);
    requires x != null;
    modifies Br, C.p;
    ensures C.p == old(C.p)[x := p];
    ensures old(C.p)[x] != null ==> Br == (old(Br)[x := true])[old(C.p)[x] := true];
    ensures old(C.p)[x] == null ==> Br == old(Br)[x := true];

procedure Set_min(x: Ref, min: int);
    requires x != null;
    modifies Br, C.min;
    ensures C.min == old(C.min)[x := min];
    ensures C.p[x] != null ==> Br == (old(Br)[x := true])[C.p[x] := true];
    ensures C.p[x] == null ==> Br == old(Br)[x := true];

procedure Set_max(x: Ref, max: int);
    requires x != null;
    modifies Br, C.max;
    ensures C.max == old(C.max)[x := max];
    ensures C.p[x] != null ==> Br == (old(Br)[x := true])[C.p[x] := true];
    ensures C.p[x] == null ==> Br == old(Br)[x := true];

procedure Set_keys(x: Ref, keys: KeySet);
    requires x != null;
    modifies Br, C.keys;
    ensures C.keys == old(C.keys)[x := keys];
    ensures C.p[x] != null ==> Br == (old(Br)[x := true])[C.p[x] := true];
    ensures C.p[x] == null ==> Br == old(Br)[x := true];

procedure Set_repr(x: Ref, repr: RefSet);
    requires x != null;
    modifies Br, C.repr;
    ensures C.repr == old(C.repr)[x := repr];
    ensures C.p[x] != null ==> Br == (old(Br)[x := true])[C.p[x] := true];
    ensures C.p[x] == null ==> Br == old(Br)[x := true];

// Broken set manipulation
procedure IfNotBr_ThenLC(x: Ref);
    ensures x != null && !Br[x] ==> LC(C.k, C.l, C.r, C.p, 
                                        C.min, C.max, C.keys, C.repr,
                                        x);

procedure AssertLCAndRemove(x: Ref);
    modifies Br;
    ensures (x != null && LC(C.k, C.l, C.r, C.p, 
                            C.min, C.max, C.keys, C.repr,
                            x)) 
                ==> Br == old(Br)[x := false];
    ensures (x == null || !LC(C.k, C.l, C.r, C.p, 
                            C.min, C.max, C.keys, C.repr, 
                            x))
                ==> Br == old(Br);

// Framing
function {:inline} Frame_k(mod_set: RefSet, old_k: [Ref]int, k: [Ref]int) returns ([Ref]int)
{
    MapIte_Ref_int(mod_set, k, old_k)
}

function {:inline} Frame_l(mod_set: RefSet, old_l: [Ref]Ref, l: [Ref]Ref) returns ([Ref]Ref)
{
    MapIte_Ref_Ref(mod_set, l, old_l)
}

function {:inline} Frame_r(mod_set: RefSet, old_r: [Ref]Ref, r: [Ref]Ref) returns ([Ref]Ref)
{
    MapIte_Ref_Ref(mod_set, r, old_r)
}

function {:inline} Frame_p(mod_set: RefSet, old_p: [Ref]Ref, p: [Ref]Ref) returns ([Ref]Ref)
{
    MapIte_Ref_Ref(mod_set, p, old_p)
}

function {:inline} Frame_min(mod_set: RefSet, old_min: [Ref]int, min: [Ref]int) returns ([Ref]int)
{
    MapIte_Ref_int(mod_set, min, old_min)
}

function {:inline} Frame_max(mod_set: RefSet, old_max: [Ref]int, max: [Ref]int) returns ([Ref]int)
{
    MapIte_Ref_int(mod_set, max, old_max)
}

function {:inline} Frame_keys(mod_set: RefSet, old_keys: [Ref]KeySet, keys: [Ref]KeySet) returns ([Ref]KeySet)
{
    MapIte_Ref_KeySet(mod_set, keys, old_keys)
}

function {:inline} Frame_repr(mod_set: RefSet, old_repr: [Ref]RefSet, repr: [Ref]RefSet) returns ([Ref]RefSet)
{
    MapIte_Ref_RefSet(mod_set, repr, old_repr)
}

function {:inline} Frame_all(
    k: [Ref]int,
    l: [Ref]Ref,
    r: [Ref]Ref,
    p: [Ref]Ref,
    min: [Ref]int,
    max: [Ref]int,
    keys: [Ref]KeySet,
    repr: [Ref]RefSet,
    oldk: [Ref]int,
    oldl: [Ref]Ref,
    oldr: [Ref]Ref,
    oldp: [Ref]Ref,
    oldmin: [Ref]int,
    oldmax: [Ref]int,
    oldkeys: [Ref]KeySet,
    oldrepr: [Ref]RefSet,
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
    && keys == Frame_keys(RefSetUnionF(mod_set, RefSetComF(old_alloc)), oldkeys, keys)
    && repr == Frame_repr(RefSetUnionF(mod_set, RefSetComF(old_alloc)), oldrepr, repr)
}

// Alloc set reasoning
function {:inline} InAlloc(
    k: [Ref]int,
    l: [Ref]Ref,
    r: [Ref]Ref,
    p: [Ref]Ref,
    min: [Ref]int,
    max: [Ref]int,
    keys: [Ref]KeySet,
    repr: [Ref]RefSet,
    x: Ref,
    alloc: RefSet
) returns (bool)
{
    x != null ==> (
        alloc[x]
        && (l[x] != null ==> alloc[l[x]])
        && (r[x] != null ==> alloc[r[x]])
        && (p[x] != null ==> alloc[p[x]])
        && RefSetSubset(repr[x], alloc)
    )
}

procedure InAllocParam(x: Ref);
    ensures x != null ==> InAlloc(C.k, C.l, C.r, C.p,
                                C.min, C.max, C.keys, C.repr,
                                x, alloc);

function {:inline} Fresh(expr: RefSet, newalloc: RefSet, oldalloc: RefSet) returns (bool)
{
    RefSetSubset(expr, newalloc)
    && RefSetsDisjoint(expr, oldalloc)
}

// Auxiliary functions
function {:inline} Isolated(
    k: [Ref]int,
    l: [Ref]Ref,
    r: [Ref]Ref,
    p: [Ref]Ref,
    min: [Ref]int,
    max: [Ref]int,
    keys: [Ref]KeySet,
    repr: [Ref]RefSet,
    x: Ref
) returns (bool)
{
  x != null ==> (
    l[x] == null
    && r[x] == null
    && p[x] == null
  )
}