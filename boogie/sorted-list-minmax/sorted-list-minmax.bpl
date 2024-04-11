// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions"
// by Adithya Murali, Cody Rivera, and P. Madhusudan.
// 
// Artifact by Cody Rivera, 2023-2024. 
//
// Definition of Sorted Lists, with min+max maps.

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
var C.next: [Ref]Ref;
var C.prev: [Ref]Ref; // ghost
var C.keys: [Ref]KeySet; // ghost
var C.repr: [Ref]RefSet; // ghost
var C.sorted: [Ref]bool; // ghost
var C.rev_sorted: [Ref]bool; // ghost
var C.min: [Ref]int; // ghost
var C.max: [Ref]int; // ghost

var Br: RefSet;
var alloc: RefSet;

// Local condition
function {:inline} LC(
    k: [Ref]int, 
    next: [Ref]Ref,
    prev: [Ref]Ref,
    keys: [Ref]KeySet,
    repr: [Ref]RefSet,
    sorted: [Ref]bool,
    rev_sorted: [Ref]bool,
    min: [Ref]int,
    max: [Ref]int,
    x: Ref
) returns (bool)
{
    x != null ==> (
        min[x] <= k[x]
        && k[x] <= max[x]
        && (prev[x] != null ==>
                !(repr[x])[prev[x]]
                && next[prev[x]] == x)
        && (next[x] == null ==>
                KeySetsEqual(keys[x], EmptyKeySet[k[x] := true])
                && RefSetsEqual(repr[x], EmptyRefSet[x := true])
                && min[x] == k[x]
                && max[x] == k[x])
        && (next[x] != null ==>
                (repr[x])[next[x]]
                && !(repr[next[x]])[x]
                && KeySetsEqual(keys[x], (keys[next[x]])[k[x] := true])
                && RefSetsEqual(repr[x], (repr[next[x]])[x := true])
                && prev[next[x]] == x
                && (sorted[x] ==> k[x] <= k[next[x]])
                && (rev_sorted[x] ==> k[x] >= k[next[x]])
                && sorted[x] == sorted[next[x]]
                && rev_sorted[x] == rev_sorted[next[x]]
                && min[x] == (if k[x] <= min[next[x]] then k[x] else min[next[x]])
                && max[x] == (if k[x] >= max[next[x]] then k[x] else max[next[x]]))
        && !(sorted[x] && rev_sorted[x])
    )
}

// Accessor Macros.
procedure Get_k(x: Ref) returns (k: int);
    requires x != null;
    ensures k == C.k[x];

procedure Get_next(x: Ref) returns (next: Ref);
    requires x != null;
    ensures next == C.next[x];
    ensures InAlloc(C.k, C.next, C.prev, 
                    C.keys, C.repr, C.sorted, C.rev_sorted, 
                    C.min, C.max, next, alloc);
    
procedure Get_prev(x: Ref) returns (prev: Ref);
    requires x != null;
    ensures prev == C.prev[x];
    ensures InAlloc(C.k, C.next, C.prev,
                    C.keys, C.repr, C.sorted, C.rev_sorted,
                    C.min, C.max, prev, alloc);

procedure Get_keys(x: Ref) returns (keys: KeySet);
    requires x != null;
    ensures keys == C.keys[x];

procedure Get_repr(x: Ref) returns (repr: RefSet);
    requires x != null;
    ensures repr == C.repr[x];
    ensures RefSetSubset(repr, alloc);

procedure Get_sorted(x: Ref) returns (sorted: bool);
    requires x != null;
    ensures sorted == C.sorted[x];

procedure Get_rev_sorted(x: Ref) returns (rev_sorted: bool);
    requires x != null;
    ensures rev_sorted == C.rev_sorted[x];

procedure Get_min(x: Ref) returns (min: int);
    requires x != null;
    ensures min == C.min[x];

procedure Get_max(x: Ref) returns (max: int);
    requires x != null;
    ensures max == C.max[x];

// Manipulation Macros
procedure Create(k: int) returns (node: Ref);
    modifies Br, alloc, C.k, C.next, C.prev;
    ensures node != null;
    ensures !old(alloc)[node];
    ensures alloc == old(alloc)[node := true];
    ensures C.k == old(C.k)[node := k];
    ensures C.next == old(C.next)[node := null];
    ensures C.prev == old(C.prev)[node := null];
    ensures Br == old(Br)[node := true];

procedure Set_k(x: Ref, k: int);
    requires x != null;
    modifies Br, C.k;
    ensures C.k == old(C.k)[x := k];
    ensures C.prev[x] != null ==> Br == (old(Br)[x := true])[C.prev[x] := true];
    ensures C.prev[x] == null ==> Br == old(Br)[x := true];

procedure Set_next(x: Ref, next: Ref);
    requires x != null;
    modifies Br, C.next;
    ensures C.next == old(C.next)[x := next];
    ensures old(C.next)[x] != null ==> Br == (old(Br)[x := true])[old(C.next)[x] := true];
    ensures old(C.next)[x] == null ==> Br == old(Br)[x := true];

procedure Set_prev(x: Ref, prev: Ref);
    requires x != null;
    modifies Br, C.prev;
    ensures C.prev == old(C.prev)[x := prev];
    ensures old(C.prev)[x] != null ==> Br == (old(Br)[x := true])[old(C.prev)[x] := true];
    ensures old(C.prev)[x] == null ==> Br == old(Br)[x := true];

procedure Set_keys(x: Ref, keys: KeySet);
    requires x != null;
    modifies Br, C.keys;
    ensures C.keys == old(C.keys)[x := keys];
    ensures C.prev[x] != null ==> Br == (old(Br)[x := true])[C.prev[x] := true];
    ensures C.prev[x] == null ==> Br == old(Br)[x := true];

procedure Set_repr(x: Ref, repr: RefSet);
    requires x != null;
    modifies Br, C.repr;
    ensures C.repr == old(C.repr)[x := repr];
    ensures C.prev[x] != null ==> Br == (old(Br)[x := true])[C.prev[x] := true];
    ensures C.prev[x] == null ==> Br == old(Br)[x := true];

procedure Set_sorted(x: Ref, sorted: bool);
    requires x != null;
    modifies Br, C.sorted;
    ensures C.sorted == old(C.sorted)[x := sorted];
    ensures C.prev[x] != null ==> Br == (old(Br)[x := true])[C.prev[x] := true];
    ensures C.prev[x] == null ==> Br == old(Br)[x := true];

procedure Set_rev_sorted(x: Ref, rev_sorted: bool);
    requires x != null;
    modifies Br, C.rev_sorted;
    ensures C.rev_sorted == old(C.rev_sorted)[x := rev_sorted];
    ensures C.prev[x] != null ==> Br == (old(Br)[x := true])[C.prev[x] := true];
    ensures C.prev[x] == null ==> Br == old(Br)[x := true];

procedure Set_min(x: Ref, min: int);
    requires x != null;
    modifies Br, C.min;
    ensures C.min == old(C.min)[x := min];
    ensures C.prev[x] != null ==> Br == (old(Br)[x := true])[C.prev[x] := true];
    ensures C.prev[x] == null ==> Br == old(Br)[x := true];

procedure Set_max(x: Ref, max: int);
    requires x != null;
    modifies Br, C.max;
    ensures C.max == old(C.max)[x := max];
    ensures C.prev[x] != null ==> Br == (old(Br)[x := true])[C.prev[x] := true];
    ensures C.prev[x] == null ==> Br == old(Br)[x := true];

// Broken Set Manipulation
procedure IfNotBr_ThenLC(x: Ref);
    ensures x != null && !Br[x] ==> LC(
        C.k, C.next, C.prev, 
        C.keys, C.repr, C.sorted, C.rev_sorted, 
        C.min, C.max, x);

procedure AssertLCAndRemove(x: Ref);
    modifies Br;
    ensures (x != null && LC(C.k, C.next, C.prev, 
                                C.keys, C.repr, C.sorted, C.rev_sorted, 
                                C.min, C.max, x)) 
                ==> Br == old(Br)[x := false];
    ensures (x == null || !LC(C.k, C.next, C.prev,
                                C.keys, C.repr, C.sorted, C.rev_sorted, 
                                C.min, C.max, x))
                ==> Br == old(Br);

// Framing
function {:inline} Frame_k(mod_set: RefSet, old_k: [Ref]int, k: [Ref]int) returns ([Ref]int)
{
    MapIte_Ref_int(mod_set, k, old_k)
}

function {:inline} Frame_next(mod_set: RefSet, old_next: [Ref]Ref, next: [Ref]Ref) returns ([Ref]Ref)
{
    MapIte_Ref_Ref(mod_set, next, old_next)
}

function {:inline} Frame_prev(mod_set: RefSet, old_prev: [Ref]Ref, prev: [Ref]Ref) returns ([Ref]Ref)
{
    MapIte_Ref_Ref(mod_set, prev, old_prev)
}

function {:inline} Frame_keys(mod_set: RefSet, old_keys: [Ref]KeySet, keys: [Ref]KeySet) returns ([Ref]KeySet)
{
    MapIte_Ref_KeySet(mod_set, keys, old_keys)
}

function {:inline} Frame_repr(mod_set: RefSet, old_repr: [Ref]RefSet, repr: [Ref]RefSet) returns ([Ref]RefSet)
{
    MapIte_Ref_RefSet(mod_set, repr, old_repr)
}

function {:inline} Frame_sorted(mod_set: RefSet, old_sorted: [Ref]bool, sorted: [Ref]bool) returns ([Ref]bool)
{
    MapIte_Ref_bool(mod_set, sorted, old_sorted)
}

function {:inline} Frame_rev_sorted(mod_set: RefSet, old_rev_sorted: [Ref]bool, rev_sorted: [Ref]bool) returns ([Ref]bool)
{
    MapIte_Ref_bool(mod_set, rev_sorted, old_rev_sorted)
}

function {:inline} Frame_min(mod_set: RefSet, old_min: [Ref]int, min: [Ref]int) returns ([Ref]int)
{
    MapIte_Ref_int(mod_set, min, old_min)
}

function {:inline} Frame_max(mod_set: RefSet, old_max: [Ref]int, max: [Ref]int) returns ([Ref]int)
{
    MapIte_Ref_int(mod_set, max, old_max)
}

function {:inline} Frame_all(
    k: [Ref]int, 
    next: [Ref]Ref,
    prev: [Ref]Ref,
    keys: [Ref]KeySet,
    repr: [Ref]RefSet,
    sorted: [Ref]bool,
    rev_sorted: [Ref]bool,
    min: [Ref]int,
    max: [Ref]int,
    oldk: [Ref]int, 
    oldnext: [Ref]Ref,
    oldprev: [Ref]Ref,
    oldkeys: [Ref]KeySet,
    oldrepr: [Ref]RefSet,
    oldsorted: [Ref]bool,
    oldrev_sorted: [Ref]bool,
    oldmin: [Ref]int,
    oldmax: [Ref]int,
    mod_set: RefSet,
    old_alloc: RefSet
) returns (bool) 
{
    k == Frame_k(RefSetUnionF(mod_set, RefSetComF(old_alloc)), oldk, k) 
    && next == Frame_next(RefSetUnionF(mod_set, RefSetComF(old_alloc)), oldnext, next) 
    && prev == Frame_prev(RefSetUnionF(mod_set, RefSetComF(old_alloc)), oldprev, prev)
    && keys == Frame_keys(RefSetUnionF(mod_set, RefSetComF(old_alloc)), oldkeys, keys)
    && repr == Frame_repr(RefSetUnionF(mod_set, RefSetComF(old_alloc)), oldrepr, repr)
    && sorted == Frame_sorted(RefSetUnionF(mod_set, RefSetComF(old_alloc)), oldsorted, sorted)
    && rev_sorted == Frame_rev_sorted(RefSetUnionF(mod_set, RefSetComF(old_alloc)), oldrev_sorted, rev_sorted)
    && min == Frame_min(RefSetUnionF(mod_set, RefSetComF(old_alloc)), oldmin, min) 
    && max == Frame_max(RefSetUnionF(mod_set, RefSetComF(old_alloc)), oldmax, max) 
}

// Alloc set reasoning
function {:inline} InAlloc(
    k: [Ref]int, 
    next: [Ref]Ref,
    prev: [Ref]Ref,
    keys: [Ref]KeySet,
    repr: [Ref]RefSet,
    sorted: [Ref]bool,
    rev_sorted: [Ref]bool,
    min: [Ref]int,
    max: [Ref]int,
    x: Ref,
    alloc: RefSet
) returns (bool)
{
  x != null ==> (
    alloc[x]
    && (next[x] != null ==> alloc[next[x]])
    && (prev[x] != null ==> alloc[prev[x]])
    && RefSetSubset(repr[x], alloc)
  )
}

procedure InAllocParam(x: Ref);
    ensures x != null ==> InAlloc(
        C.k, C.next, C.prev, C.keys, 
        C.repr, C.sorted, C.rev_sorted, 
        C.min, C.max, x, alloc);

function {:inline} Fresh(expr: RefSet, newalloc: RefSet, oldalloc: RefSet) returns (bool)
{
    RefSetSubset(expr, newalloc)
    && RefSetsDisjoint(expr, oldalloc)
}

// Auxiliary functions
function {:inline} Isolated(
    k: [Ref]int, 
    next: [Ref]Ref,
    prev: [Ref]Ref,
    keys: [Ref]KeySet,
    repr: [Ref]RefSet,
    sorted: [Ref]bool,
    rev_sorted: [Ref]bool,
    min: [Ref]int,
    max: [Ref]int,
    x: Ref
) returns (bool)
{
  x != null ==> (
    next[x] == null
    && prev[x] == null
  )
}