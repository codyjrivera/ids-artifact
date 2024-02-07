// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions of Data Structures"
// by Anonymous Authors.
// 
// Artifact by Anonymous Author, 2023. 
//
// Definition of Single Linked Lists.

// Datatype aliases
type Ref = int;
const null: Ref;

type KeySet = [int]bool;
type RefSet = [Ref]bool;

type IntSet = [int]bool;
function {:builtin "MapAdd"} mapadd([int]int, [int]int) : [int]int;
function {:builtin "MapSub"} mapsub([int]int, [int]int) : [int]int;
function {:builtin "MapMul"} mapmul([int]int, [int]int) : [int]int;
function {:builtin "MapDiv"} mapdiv([int]int, [int]int) : [int]int;
function {:builtin "MapMod"} mapmod([int]int, [int]int) : [int]int;
function {:builtin "MapConst"} mapconstint(int) : [int]int;
function {:builtin "MapConst"} mapconstbool(bool) : [int]bool;
function {:builtin "MapAnd"} mapand([int]bool, [int]bool) : [int]bool;
function {:builtin "MapOr"} mapor([int]bool, [int]bool) : [int]bool;
function {:builtin "MapNot"} mapnot([int]bool) : [int]bool;
function {:builtin "MapIte"} mapiteint([int]bool, [int]int, [int]int) : [int]int;
function {:builtin "MapIte"} mapitebool([int]bool, [int]bool, [int]bool) : [int]bool;
function {:builtin "MapIte"} mapiteintset([int]bool, [int]IntSet, [int]IntSet) : [int]IntSet;
function {:builtin "MapLe"} maple([int]int, [int]int) : [int]bool;
function {:builtin "MapLt"} maplt([int]int, [int]int) : [int]bool;
function {:builtin "MapGe"} mapge([int]int, [int]int) : [int]bool;
function {:builtin "MapGt"} mapgt([int]int, [int]int) : [int]bool;
function {:builtin "MapEq"} mapeq([int]int, [int]int) : [int]bool;
function {:builtin "MapIff"} mapiff([int]bool, [int]bool) : [int]bool;
function {:builtin "MapImp"} mapimp([int]bool, [int]bool) : [int]bool;

// Set library
const EmptyKeySet: KeySet;
axiom EmptyKeySet == mapconstbool(false);

function {:inline} KeySetsEqual(s1: KeySet, s2: KeySet) returns (bool)
{
    s1 == s2 // WARNING: (==) symbol doesn't guarantee extensionality of equality.
             // (though it seems to do so in the current transformation).
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
    mapand(s1, s2)
}

function {:inline} KeySetUnionF(s1: KeySet, s2: KeySet) returns (KeySet)
{
    mapor(s1, s2)
}

function {:inline} KeySetComF(s: KeySet) returns (KeySet)
{
    mapnot(s)
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
axiom EmptyRefSet == mapconstbool(false);

function {:inline} RefSetsEqual(s1: RefSet, s2: RefSet) returns (bool)
{
    s1 == s2 // WARNING: (==) symbol doesn't guarantee extensionality of equality.
             // (though it seems to do so in the current transformation).
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
    mapand(s1, s2)
}

function {:inline} RefSetUnionF(s1: RefSet, s2: RefSet) returns (RefSet)
{
    mapor(s1, s2)
}

function {:inline} RefSetComF(s: RefSet) returns (RefSet)
{
    mapnot(s)
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

var Br: RefSet;
var alloc: RefSet;

// Local condition
function {:inline} LC(
    k: [Ref]int, 
    next: [Ref]Ref,
    prev: [Ref]Ref,
    keys: [Ref]KeySet,
    repr: [Ref]RefSet,
    x: Ref
) returns (bool)
{
    x != null ==> (
        (prev[x] != null ==>
            !(repr[x])[prev[x]]
            && next[prev[x]] == x)
        && (next[x] == null ==>
                KeySetsEqual(keys[x], EmptyKeySet[k[x] := true])
                && RefSetsEqual(repr[x], EmptyRefSet[x := true]))
        && (next[x] != null ==>
                (repr[x])[next[x]]
                && !(repr[next[x]])[x]
                && KeySetsEqual(keys[x], (keys[next[x]])[k[x] := true])
                && RefSetsEqual(repr[x], (repr[next[x]])[x := true])
                && prev[next[x]] == x)
    )
}

// Accessor Macros.
procedure Get_k(x: Ref) returns (k: int);
    requires x != null;
    ensures k == C.k[x];

procedure Get_next(x: Ref) returns (next: Ref);
    requires x != null;
    ensures next == C.next[x];
    ensures InAlloc(C.k, C.next, C.prev, C.keys, C.repr, next, alloc);
    
procedure Get_prev(x: Ref) returns (prev: Ref);
    requires x != null;
    ensures prev == C.prev[x];
    ensures InAlloc(C.k, C.next, C.prev, C.keys, C.repr, prev, alloc);

procedure Get_keys(x: Ref) returns (keys: KeySet);
    requires x != null;
    ensures keys == C.keys[x];

procedure Get_repr(x: Ref) returns (repr: RefSet);
    requires x != null;
    ensures repr == C.repr[x];
    ensures RefSetSubset(repr, alloc);

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

// Broken Set Manipulation
procedure IfNotBr_ThenLC(x: Ref);
    ensures x != null && !Br[x] ==> LC(C.k, C.next, C.prev, C.keys, C.repr, x);

procedure AssertLCAndRemove(x: Ref);
    modifies Br;
    ensures (x != null && LC(C.k, C.next, C.prev, C.keys, C.repr, x)) 
                ==> Br == old(Br)[x := false];
    ensures (x == null || !LC(C.k, C.next, C.prev, C.keys, C.repr, x))
                ==> Br == old(Br);

// Framing
function {:inline} Frame_k(mod_set: RefSet, old_k: [Ref]int, k: [Ref]int) returns ([Ref]int)
{
    mapiteint(mod_set, k, old_k)
}

function {:inline} Frame_next(mod_set: RefSet, old_next: [Ref]Ref, next: [Ref]Ref) returns ([Ref]Ref)
{
    mapiteint(mod_set, next, old_next)
}

function {:inline} Frame_prev(mod_set: RefSet, old_prev: [Ref]Ref, prev: [Ref]Ref) returns ([Ref]Ref)
{
    mapiteint(mod_set, prev, old_prev)
}

function {:inline} Frame_keys(mod_set: RefSet, old_keys: [Ref]KeySet, keys: [Ref]KeySet) returns ([Ref]KeySet)
{
    mapiteintset(mod_set, keys, old_keys)
}

function {:inline} Frame_repr(mod_set: RefSet, old_repr: [Ref]RefSet, repr: [Ref]RefSet) returns ([Ref]RefSet)
{
    mapiteintset(mod_set, repr, old_repr)
}

function {:inline} Frame_all(
    k: [Ref]int, 
    next: [Ref]Ref,
    prev: [Ref]Ref,
    keys: [Ref]KeySet,
    repr: [Ref]RefSet,
    oldk: [Ref]int, 
    oldnext: [Ref]Ref,
    oldprev: [Ref]Ref,
    oldkeys: [Ref]KeySet,
    oldrepr: [Ref]RefSet,
    mod_set: RefSet,
    old_alloc: RefSet
) returns (bool) 
{
    k == Frame_k(RefSetUnionF(mod_set, RefSetComF(old_alloc)), oldk, k) 
    && next == Frame_next(RefSetUnionF(mod_set, RefSetComF(old_alloc)), oldnext, next) 
    && prev == Frame_prev(RefSetUnionF(mod_set, RefSetComF(old_alloc)), oldprev, prev)
    && keys == Frame_keys(RefSetUnionF(mod_set, RefSetComF(old_alloc)), oldkeys, keys)
    && repr == Frame_repr(RefSetUnionF(mod_set, RefSetComF(old_alloc)), oldrepr, repr)
}

// Alloc set reasoning
function {:inline} InAlloc(
    k: [Ref]int, 
    next: [Ref]Ref,
    prev: [Ref]Ref,
    keys: [Ref]KeySet,
    repr: [Ref]RefSet,
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
    ensures x != null ==> InAlloc(C.k, C.next, C.prev, C.keys, C.repr, x, alloc);

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
    x: Ref
) returns (bool)
{
  x != null ==> (
    next[x] == null
    && prev[x] == null
  )
}