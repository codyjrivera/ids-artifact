// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions of Data Structures"
// by Anonymous Authors.
// 
// Artifact by Anonymous Author, 2023. 
//
// Definition of Treaps.

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
var C.prio: [Ref]int;
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
    prio: [Ref]int,
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
                && max[l[x]] < k[x]
                && prio[l[x]] <= prio[x])
        && (r[x] != null ==> 
                (repr[x])[r[x]]
                && !(repr[r[x]])[x]
                && p[r[x]] == x
                && min[r[x]] > k[x]
                && prio[r[x]] <= prio[x])
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

procedure Get_prio(x: Ref) returns (prio: int);
    requires x != null;
    ensures prio == C.prio[x];

procedure Get_l(x: Ref) returns (l: Ref);
    requires x != null;
    ensures l == C.l[x];
    ensures InAlloc(C.k, C.prio, C.l, C.r, C.p, 
                C.min, C.max, C.keys, C.repr, 
                l, alloc);

procedure Get_r(x: Ref) returns (r: Ref);
    requires x != null;
    ensures r == C.r[x];
    ensures InAlloc(C.k, C.prio, C.l, C.r, C.p, 
                C.min, C.max, C.keys, C.repr, 
                r, alloc);

procedure Get_p(x: Ref) returns (p: Ref);
    requires x != null;
    ensures p == C.p[x];
    ensures InAlloc(C.k, C.prio, C.l, C.r, C.p, 
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
procedure Create(k: int, prio: int) returns (node: Ref);
    modifies Br, alloc, C.k, C.prio, C.l, C.r, C.p;
    ensures node != null;
    ensures !old(alloc)[node];
    ensures alloc == old(alloc)[node := true];
    ensures C.k == old(C.k)[node := k];
    ensures C.prio == old(C.prio)[node := prio];
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

procedure Set_prio(x: Ref, prio: int);
    requires x != null;
    modifies Br, C.prio;
    ensures C.prio == old(C.prio)[x := prio];
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
    ensures x != null && !Br[x] ==> LC(C.k, C.prio, C.l, C.r, C.p, 
                                        C.min, C.max, C.keys, C.repr,
                                        x);

procedure AssertLCAndRemove(x: Ref);
    modifies Br;
    ensures (x != null && LC(C.k, C.prio, C.l, C.r, C.p, 
                            C.min, C.max, C.keys, C.repr,
                            x)) 
                ==> Br == old(Br)[x := false];
    ensures (x == null || !LC(C.k, C.prio, C.l, C.r, C.p, 
                            C.min, C.max, C.keys, C.repr, 
                            x))
                ==> Br == old(Br);

// Framing
function Frame_k(mod_set: RefSet, old_k: [Ref]int, k: [Ref]int) returns ([Ref]int);
function Frame_prio(mod_set: RefSet, old_prio: [Ref]int, prio: [Ref]int) returns ([Ref]int);
function Frame_l(mod_set: RefSet, old_l: [Ref]Ref, l: [Ref]Ref) returns ([Ref]Ref);
function Frame_r(mod_set: RefSet, old_r: [Ref]Ref, r: [Ref]Ref) returns ([Ref]Ref);
function Frame_p(mod_set: RefSet, old_p: [Ref]Ref, p: [Ref]Ref) returns ([Ref]Ref);
function Frame_min(mod_set: RefSet, old_min: [Ref]int, min: [Ref]int) returns ([Ref]int);
function Frame_max(mod_set: RefSet, old_max: [Ref]int, max: [Ref]int) returns ([Ref]int);
function Frame_keys(mod_set: RefSet, old_keys: [Ref]KeySet, keys: [Ref]KeySet) returns ([Ref]KeySet);
function Frame_repr(mod_set: RefSet, old_repr: [Ref]RefSet, repr: [Ref]RefSet) returns ([Ref]RefSet);

function {:inline} Frame_all(
    k: [Ref]int,
    prio: [Ref]int, 
    l: [Ref]Ref,
    r: [Ref]Ref,
    p: [Ref]Ref,
    min: [Ref]int,
    max: [Ref]int,
    keys: [Ref]KeySet,
    repr: [Ref]RefSet,
    oldk: [Ref]int,
    oldprio: [Ref]int, 
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
    && prio == Frame_prio(RefSetUnionF(mod_set, RefSetComF(old_alloc)), oldprio, prio)
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
    prio: [Ref]int,
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
    ensures x != null ==> InAlloc(C.k, C.prio, C.l, C.r, C.p,
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
    prio: [Ref]int, 
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