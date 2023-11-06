// Sorted List Insert
// Cody Rivera

// Datatype aliases
type Ref;
const null: Ref;

type KeySet = [int]bool;
type RefSet = [Ref]bool;

// Define necessary set operations and constants.

// Operations and constants for key sets.
const EmptyKeySet: KeySet;

function KeySetUnionF(s1: KeySet, s2: KeySet) returns (KeySet);

function KeySetDiffF(s1: KeySet, s2: KeySet) returns (KeySet);

function KeySetsEqual(s1: KeySet, s2: KeySet) returns (bool);

function KeySetsDisjoint(s1: KeySet, s2: KeySet) returns (bool);

// Operations and constants for reference sets.
const EmptyRefSet: RefSet;

function RefSetUnionF(s1: RefSet, s2: RefSet) returns (RefSet);

function RefSetDiffF(s1: RefSet, s2: RefSet) returns (RefSet);

function RefSetSubset(s1: RefSet, s2: RefSet) returns (bool);

function RefSetsEqual(s1: RefSet, s2: RefSet) returns (bool);

function RefSetsDisjoint(s1: RefSet, s2: RefSet) returns (bool);

// Frame Reasoning
function Frame_k(mod_set: RefSet, old_k: [Ref]int, k: [Ref]int) returns ([Ref]int);

// axiom (forall mod_set: RefSet, old_k: [Ref]int, k: [Ref]int, o: Ref ::
//     { Frame_k(mod_set, old_k, k)[o] }
//     Frame_k(mod_set, old_k, k)[o] == (if !mod_set[o] then old_k[o] else k[o]));

function Frame_next(mod_set: RefSet, old_next: [Ref]Ref, next: [Ref]Ref) returns ([Ref]Ref);

// axiom (forall mod_set: RefSet, old_next: [Ref]Ref, next: [Ref]Ref, o: Ref ::
//     { Frame_next(mod_set, old_next, next)[o] }
//     Frame_next(mod_set, old_next, next)[o] == (if !mod_set[o] then old_next[o] else next[o]));

function Frame_prev(mod_set: RefSet, old_prev: [Ref]Ref, prev: [Ref]Ref) returns ([Ref]Ref);

// axiom (forall mod_set: RefSet, old_prev: [Ref]Ref, prev: [Ref]Ref, o: Ref ::
//     { Frame_prev(mod_set, old_prev, prev)[o] }
//     Frame_prev(mod_set, old_prev, prev)[o] == (if !mod_set[o] then old_prev[o] else prev[o]));

function Frame_keys(mod_set: RefSet, old_keys: [Ref]KeySet, keys: [Ref]KeySet) returns ([Ref]KeySet);

// axiom (forall mod_set: RefSet, old_keys: [Ref]KeySet, keys: [Ref]KeySet, o: Ref ::
//     { Frame_keys(mod_set, old_keys, keys)[o] }
//     Frame_keys(mod_set, old_keys, keys)[o] == (if !mod_set[o] then old_keys[o] else keys[o]));

function Frame_repr(mod_set: RefSet, old_repr: [Ref]RefSet, repr: [Ref]RefSet) returns ([Ref]RefSet);

// axiom (forall mod_set: RefSet, old_repr: [Ref]RefSet, repr: [Ref]RefSet, o: Ref ::
//     { Frame_repr(mod_set, old_repr, repr)[o] }
//     Frame_repr(mod_set, old_repr, repr)[o] == (if !mod_set[o] then old_repr[o] else repr[o]));

function Frame_sorted(mod_set: RefSet, old_sorted: [Ref]bool, sorted: [Ref]bool) returns ([Ref]bool);

// axiom (forall mod_set: RefSet, old_sorted: [Ref]bool, sorted: [Ref]bool, o: Ref ::
//     { Frame_sorted(mod_set, old_sorted, sorted)[o] }
//     Frame_sorted(mod_set, old_sorted, sorted)[o] == (if !mod_set[o] then old_sorted[o] else sorted[o]));

// Alloc set reasoning:
function {:inline} InAlloc(
    k: [Ref]int, 
    next: [Ref]Ref,
    prev: [Ref]Ref,
    keys: [Ref]KeySet,
    repr: [Ref]RefSet,
    sorted: [Ref]bool,
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

// // Axioms for quick checking -- I can easily comment these.
// // Operations and constants for key sets.
// axiom (forall o: int :: { EmptyKeySet[o] } !EmptyKeySet[o]);

// axiom (forall a: KeySet, b: KeySet, o: int :: 
//   { KeySetUnionF(a, b)[o] } 
//   KeySetUnionF(a, b)[o] <==> a[o] || b[o]);

// axiom (forall a: KeySet, b: KeySet, y: int :: 
//   { KeySetUnionF(a, b), a[y] } 
//   a[y] ==> KeySetUnionF(a, b)[y]);

// axiom (forall a: KeySet, b: KeySet, y: int :: 
//   { KeySetUnionF(a, b), b[y] } 
//   b[y] ==> KeySetUnionF(a, b)[y]);

// axiom (forall a: KeySet, b: KeySet :: 
//   { KeySetUnionF(a, b) } 
//   KeySetsDisjoint(a, b)
//      ==> KeySetsEqual(KeySetDiffF(KeySetUnionF(a, b), a), b)
//        && KeySetsEqual(KeySetDiffF(KeySetUnionF(a, b), b), a));

// axiom (forall a: KeySet, b: KeySet, o: int ::
//   { KeySetDiffF(a, b)[o] } 
//   KeySetDiffF(a, b)[o] <==> a[o] && !b[o]);

// axiom (forall a: KeySet, b: KeySet, y: int ::
//   { KeySetDiffF(a, b), b[y] } 
//   b[y] ==> !KeySetDiffF(a, b)[y]);

// axiom (forall a: KeySet, b: KeySet :: 
//   { KeySetsEqual(a, b) } 
//   KeySetsEqual(a, b) <==> (forall o: int :: { a[o] } { b[o] } a[o] <==> b[o]));

// axiom (forall a: KeySet, b: KeySet :: 
//   { KeySetsEqual(a, b) } 
//   KeySetsEqual(a, b) ==> a == b);

// axiom (forall a: KeySet, b: KeySet :: 
//   { KeySetsDisjoint(a, b) } 
//   KeySetsDisjoint(a, b) <==> (forall o: int :: { a[o] } { b[o] } !a[o] || !b[o]));

// // Operations and constants for reference sets.
// axiom (forall o: Ref :: { EmptyRefSet[o] } !EmptyRefSet[o]);

// axiom (forall a: RefSet, b: RefSet, o: Ref :: 
//   { RefSetUnionF(a, b)[o] } 
//   RefSetUnionF(a, b)[o] <==> a[o] || b[o]);

// axiom (forall a: RefSet, b: RefSet, y: Ref :: 
//   { RefSetUnionF(a, b), a[y] } 
//   a[y] ==> RefSetUnionF(a, b)[y]);

// axiom (forall a: RefSet, b: RefSet, y: Ref :: 
//   { RefSetUnionF(a, b), b[y] } 
//   b[y] ==> RefSetUnionF(a, b)[y]);

// axiom (forall a: RefSet, b: RefSet :: 
//   { RefSetUnionF(a, b) } 
//   RefSetsDisjoint(a, b)
//      ==> RefSetsEqual(RefSetDiffF(RefSetUnionF(a, b), a), b)
//        && RefSetsEqual(RefSetDiffF(RefSetUnionF(a, b), b), a));

// axiom (forall a: RefSet, b: RefSet, o: Ref ::
//   { RefSetDiffF(a, b)[o] } 
//   RefSetDiffF(a, b)[o] <==> a[o] && !b[o]);

// axiom (forall a: RefSet, b: RefSet, y: Ref ::
//   { RefSetDiffF(a, b), b[y] } 
//   b[y] ==> !RefSetDiffF(a, b)[y]);

// axiom (forall a: RefSet, b: RefSet :: 
//   { RefSetSubset(a, b) } 
//   RefSetSubset(a, b) <==> (forall o: Ref :: { a[o] } { b[o] } a[o] ==> b[o]));

// axiom (forall a: RefSet, b: RefSet :: 
//   { RefSetsEqual(a, b) } 
//   RefSetsEqual(a, b) <==> (forall o: Ref :: { a[o] } { b[o] } a[o] <==> b[o]));

// axiom (forall a: RefSet, b: RefSet :: 
//   { RefSetsEqual(a, b) } 
//   RefSetsEqual(a, b) ==> a == b);

// axiom (forall a: RefSet, b: RefSet :: 
//   { RefSetsDisjoint(a, b) } 
//   RefSetsDisjoint(a, b) <==> (forall o: Ref :: { a[o] } { b[o] } !a[o] || !b[o]));


// Define fields
var C.k: [Ref]int;
var C.next: [Ref]Ref;
var C.prev: [Ref]Ref;
var C.keys: [Ref]KeySet;
var C.repr: [Ref]RefSet;
var C.sorted: [Ref]bool;

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
                && prev[next[x]] == x
                && (sorted[x] ==> k[x] <= k[next[x]])
                && sorted[x] == sorted[next[x]])
    )
}

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
    modifies Br, C.k;
    ensures C.k == old(C.k)[x := k];
    ensures C.prev[x] != null ==> Br == (old(Br)[x := true])[C.prev[x] := true];
    ensures C.prev[x] == null ==> Br == old(Br)[x := true];

procedure Set_next(x: Ref, next: Ref);
    modifies Br, C.next;
    ensures C.next == old(C.next)[x := next];
    ensures old(C.next)[x] != null ==> Br == (old(Br)[x := true])[old(C.next)[x] := true];
    ensures old(C.next)[x] == null ==> Br == old(Br)[x := true];

procedure Set_prev(x: Ref, prev: Ref);
    modifies Br, C.prev;
    ensures C.prev == old(C.prev)[x := prev];
    ensures old(C.prev)[x] != null ==> Br == (old(Br)[x := true])[old(C.prev)[x] := true];
    ensures old(C.prev)[x] == null ==> Br == old(Br)[x := true];

procedure Set_keys(x: Ref, keys: KeySet);
    modifies Br, C.keys;
    ensures C.keys == old(C.keys)[x := keys];
    ensures C.prev[x] != null ==> Br == (old(Br)[x := true])[C.prev[x] := true];
    ensures C.prev[x] == null ==> Br == old(Br)[x := true];

procedure Set_repr(x: Ref, repr: RefSet);
    modifies Br, C.repr;
    ensures C.repr == old(C.repr)[x := repr];
    ensures C.prev[x] != null ==> Br == (old(Br)[x := true])[C.prev[x] := true];
    ensures C.prev[x] == null ==> Br == old(Br)[x := true];

procedure Set_sorted(x: Ref, sorted: bool);
    modifies Br, C.sorted;
    ensures C.sorted == old(C.sorted)[x := sorted];
    ensures C.prev[x] != null ==> Br == (old(Br)[x := true])[C.prev[x] := true];
    ensures C.prev[x] == null ==> Br == old(Br)[x := true];

// Broken Set Manipulation
procedure IfNotBr_ThenLC(x: Ref);
    ensures x != null && !Br[x] ==> LC(C.k, C.next, C.prev, C.keys, C.repr, C.sorted, x);

procedure AssertLCAndRemove(x: Ref);
    modifies Br;
    ensures (x != null && LC(C.k, C.next, C.prev, C.keys, C.repr, C.sorted, x)) 
                ==> Br == old(Br)[x := false];
    ensures (x == null || !LC(C.k, C.next, C.prev, C.keys, C.repr, C.sorted, x))
                ==> Br == old(Br);

function {:inline} fresh(expr: RefSet, newalloc: RefSet, oldalloc: RefSet) returns (bool)
{
    RefSetSubset(expr, newalloc)
    && RefSetsDisjoint(expr, oldalloc)
    && RefSetSubset(oldalloc, newalloc) // try to see if can be rewritten elsewhere
}
