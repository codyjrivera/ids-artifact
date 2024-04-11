// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions"
// by Adithya Murali, Cody Rivera, and P. Madhusudan.
// 
// Artifact by Cody Rivera, 2023. 
//
// Definition of Circular Lists.

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
var C.next: [Ref]Ref;
var C.prev: [Ref]Ref; // ghost
var C.last: [Ref]Ref; // ghost
var C.len: [Ref]int; // ghost
var C.rlen: [Ref]int; // ghost
var C.keys: [Ref]KeySet; // ghost
var C.repr: [Ref]RefSet; // ghost

var Br: RefSet;
var alloc: RefSet;

// Local condition
function {:inline} LC(
    k: [Ref]int, 
    next: [Ref]Ref,
    prev: [Ref]Ref,
    last: [Ref]Ref,
    len: [Ref]int,
    rlen: [Ref]int,
    keys: [Ref]KeySet,
    repr: [Ref]RefSet,
    x: Ref
) returns (bool)
{
    x != null ==> (
        next[prev[x]] == x
        && prev[next[x]] == x
        && (x == last[x] ==>
                len[x] == 0
                && rlen[x] == 0
                && last[x] == last[next[x]]
                && (next[x] == x ==>
                        KeySetsEqual(keys[x], EmptyKeySet)
                        && RefSetsEqual(repr[x], EmptyRefSet[x := true]))
                && (next[x] != x ==>
                        KeySetsEqual(keys[x], keys[next[x]])
                        && RefSetsEqual(repr[x], (repr[next[x]])[x := true])
                        && !(repr[next[x]])[x]))
        && (x != last[x] ==>
                len[x] == len[next[x]] + 1
                && rlen[x] == rlen[prev[x]] + 1
                && (next[x] == last[x] ==>
                        KeySetsEqual(keys[x], EmptyKeySet[k[x] := true])
                        && RefSetsEqual(repr[x], EmptyRefSet[x := true]))
                && (next[x] != last[x] ==>
                        KeySetsEqual(keys[x], (keys[next[x]])[k[x] := true])
                        && RefSetsEqual(repr[x], (repr[next[x]])[x := true])
                        && !(repr[next[x]])[x])
                && last[x] == last[next[x]]
                && last[last[x]] == last[x]
                && (repr[last[x]])[x]
                && (repr[last[x]])[prev[x]]
                && (repr[last[x]])[next[x]])
        && next[x] != null
        && prev[x] != null
        && last[x] != null
        && len[x] >= 0
        && rlen[x] >= 0
    )
}

function {:inline} LC_Trans_MinusNode(
    k: [Ref]int, 
    next: [Ref]Ref,
    prev: [Ref]Ref,
    last: [Ref]Ref,
    len: [Ref]int,
    rlen: [Ref]int,
    keys: [Ref]KeySet,
    repr: [Ref]RefSet,
    x: Ref,
    n: Ref
) returns (bool)
{
    x != null && n != null ==> (
        next[prev[x]] == x
        && prev[next[x]] == x
        && (x == last[x] ==>
                len[x] == 0
                && rlen[x] == 0
                && last[x] == last[next[x]]
                && (next[x] == x ==>
                        KeySetsEqual(keys[x], EmptyKeySet)
                        && RefSetsEqual(repr[x], EmptyRefSet[x := true]))
                && (next[x] != x ==>
                        (KeySetsEqual(keys[x], (keys[next[x]])[k[n] := false])
                            || KeySetsEqual(keys[x], keys[next[x]]))
                        // We've already updated the repr
                        && RefSetsEqual(repr[x], (repr[next[x]])[x := true])
                        && !(repr[next[x]])[x]))
        && (x != last[x] ==>
                len[x] == len[next[x]]
                && rlen[x] == rlen[prev[x]] + 1
                && (next[x] == last[x] ==>
                        KeySetsEqual(keys[x], EmptyKeySet[k[x] := true])
                        && RefSetsEqual(repr[x], EmptyRefSet[x := true]))
                && (next[x] != last[x] ==>
                        (KeySetsEqual(keys[x], ((keys[next[x]])[k[x] := true])[k[n] := false])
                            || KeySetsEqual(keys[x], (keys[next[x]])[k[x] := true]))
                        && RefSetsEqual(repr[x], ((repr[next[x]])[x := true])[n := false])
                        && !(repr[next[x]])[x])
                && last[x] == last[next[x]]
                //&& last[last[x]] == last[x]
                && (repr[last[x]])[x]
                && (repr[last[x]])[prev[x]]
                && (repr[last[x]])[next[x]])
        && next[x] != null
        && prev[x] != null
        && last[x] != null
        && len[x] >= 0
        && rlen[x] >= 0
    )
}

function {:inline} LC_Trans_PlusNode(
    k: [Ref]int, 
    next: [Ref]Ref,
    prev: [Ref]Ref,
    last: [Ref]Ref,
    len: [Ref]int,
    rlen: [Ref]int,
    keys: [Ref]KeySet,
    repr: [Ref]RefSet,
    x: Ref,
    n: Ref
) returns (bool)
{
    x != null && n != null ==> (
        next[prev[x]] == x
        && prev[next[x]] == x
        && (x == last[x] ==>
                len[x] == 0
                && rlen[x] == 0
                && last[x] == last[next[x]]
                && (next[x] == x ==>
                        KeySetsEqual(keys[x], EmptyKeySet)
                        && RefSetsEqual(repr[x], EmptyRefSet[x := true]))
                && (next[x] != x ==>
                        (KeySetsEqual(keys[x], (keys[next[x]])[k[n] := true])
                            || KeySetsEqual(keys[x], keys[next[x]]))
                        && RefSetsEqual(repr[x], ((repr[next[x]])[x := true])[n := true])
                        && !(repr[next[x]])[x]))
        && (x != last[x] ==>
                len[x] == len[next[x]] + 2
                && rlen[x] == rlen[prev[x]] + 1
                && (next[x] == last[x] ==>
                        KeySetsEqual(keys[x], EmptyKeySet[k[x] := true])
                        && RefSetsEqual(repr[x], EmptyRefSet[x := true]))
                && (next[x] != last[x] ==>
                        (KeySetsEqual(keys[x], ((keys[next[x]])[k[x] := true])[k[n] := true])
                            || KeySetsEqual(keys[x], (keys[next[x]])[k[x] := true]))
                        && RefSetsEqual(repr[x], ((repr[next[x]])[x := true])[n := true])
                        && !(repr[next[x]])[x])
                && last[x] == last[next[x]]
                //&& last[last[x]] == last[x]
                && (repr[last[x]])[x]
                && (repr[last[x]])[prev[x]]
                && (repr[last[x]])[next[x]])
        && next[x] != null
        && prev[x] != null
        && last[x] != null
        && len[x] >= 0
        && rlen[x] >= 0
    )
}

function {:inline} LC_At_Last(
    k: [Ref]int, 
    next: [Ref]Ref,
    prev: [Ref]Ref,
    last: [Ref]Ref,
    len: [Ref]int,
    rlen: [Ref]int,
    keys: [Ref]KeySet,
    repr: [Ref]RefSet,
    x: Ref,
    n: Ref
) returns (bool)
{
    x != null ==> (
        next[prev[x]] == x
        && prev[next[x]] == x
        && (x == last[x] ==>
                len[x] == 0
                && rlen[x] == 0
                && last[x] == last[next[x]]
                && (next[x] == x ==>
                        KeySetsEqual(keys[x], EmptyKeySet)
                        && RefSetsEqual(repr[x], EmptyRefSet[x := true]))
                && (next[x] != x ==>
                        KeySetsEqual(keys[x], keys[next[x]])
                        && RefSetsEqual(repr[x], ((repr[next[x]])[x := true])[n := true])
                        && !(repr[next[x]])[x]))
        && (x != last[x] ==>
                len[x] == len[next[x]] + 1
                && rlen[x] == rlen[prev[x]] + 1
                && (next[x] == last[x] ==>
                        KeySetsEqual(keys[x], EmptyKeySet[k[x] := true])
                        && RefSetsEqual(repr[x], EmptyRefSet[x := true]))
                && (next[x] != last[x] ==>
                        KeySetsEqual(keys[x], (keys[next[x]])[k[x] := true])
                        && RefSetsEqual(repr[x], (repr[next[x]])[x := true])
                        && !(repr[next[x]])[x])
                && last[x] == last[next[x]]
                && last[last[x]] == last[x]
                && (repr[last[x]])[x]
                && (repr[last[x]])[prev[x]]
                && (repr[last[x]])[next[x]])
        && next[x] != null
        && prev[x] != null
        && last[x] != null
        && len[x] >= 0
        && rlen[x] >= 0
    )
}

function {:inline} LC_Trans_NoRlen(
    k: [Ref]int, 
    next: [Ref]Ref,
    prev: [Ref]Ref,
    last: [Ref]Ref,
    len: [Ref]int,
    rlen: [Ref]int,
    keys: [Ref]KeySet,
    repr: [Ref]RefSet,
    x: Ref
) returns (bool)
{
    x != null ==> (
        next[prev[x]] == x
        && prev[next[x]] == x
        && (x == last[x] ==>
                len[x] == 0
                //&& rlen[x] == 0
                && last[x] == last[next[x]]
                && (next[x] == x ==>
                        KeySetsEqual(keys[x], EmptyKeySet)
                        && RefSetsEqual(repr[x], EmptyRefSet[x := true]))
                && (next[x] != x ==>
                        KeySetsEqual(keys[x], keys[next[x]])
                        && RefSetsEqual(repr[x], (repr[next[x]])[x := true])
                        && !(repr[next[x]])[x]))
        && (x != last[x] ==>
                len[x] == len[next[x]] + 1
                //&& rlen[x] == rlen[prev[x]] + 1
                && (next[x] == last[x] ==>
                        KeySetsEqual(keys[x], EmptyKeySet[k[x] := true])
                        && RefSetsEqual(repr[x], EmptyRefSet[x := true]))
                && (next[x] != last[x] ==>
                        KeySetsEqual(keys[x], (keys[next[x]])[k[x] := true])
                        && RefSetsEqual(repr[x], (repr[next[x]])[x := true])
                        && !(repr[next[x]])[x])
                && last[x] == last[next[x]]
                && last[last[x]] == last[x]
                && (repr[last[x]])[x]
                && (repr[last[x]])[prev[x]]
                && (repr[last[x]])[next[x]])
        && next[x] != null
        && prev[x] != null
        && last[x] != null
        && len[x] >= 0
        && rlen[x] >= 0
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
                    C.last, C.len, C.rlen,
                    C.keys, C.repr, next, alloc);
    
procedure Get_prev(x: Ref) returns (prev: Ref);
    requires x != null;
    ensures prev == C.prev[x];
    ensures InAlloc(C.k, C.next, C.prev, 
                    C.last, C.len, C.rlen,
                    C.keys, C.repr, prev, alloc);

procedure Get_last(x: Ref) returns (last: Ref);
    requires x != null;
    ensures last == C.last[x];
    ensures InAlloc(C.k, C.next, C.prev, 
                    C.last, C.len, C.rlen,
                    C.keys, C.repr, last, alloc);

procedure Get_len(x: Ref) returns (len: int);
    requires x != null;
    ensures len == C.len[x];

procedure Get_rlen(x: Ref) returns (rlen: int);
    requires x != null;
    ensures rlen == C.rlen[x];

procedure Get_keys(x: Ref) returns (keys: KeySet);
    requires x != null;
    ensures keys == C.keys[x];

procedure Get_repr(x: Ref) returns (repr: RefSet);
    requires x != null;
    ensures repr == C.repr[x];
    ensures RefSetSubset(repr, alloc);

// Manipulation Macros
procedure Create(k: int) returns (node: Ref);
    modifies Br, alloc, C.k, C.next, C.prev, C.last, C.repr;
    ensures node != null;
    ensures !old(alloc)[node];
    ensures alloc == old(alloc)[node := true];
    ensures C.k == old(C.k)[node := k];
    ensures C.next == old(C.next)[node := node];
    ensures C.prev == old(C.prev)[node := node];
    ensures C.last == old(C.last)[node := node];
    ensures C.repr == old(C.repr)[node := EmptyRefSet[node := true]];
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

procedure Set_last(x: Ref, last: Ref);
    requires x != null;
    requires C.last[x] != x || (C.last[x] == x && RefSetsEqual(C.repr[x], EmptyRefSet[x := true]));
    modifies Br, C.last;
    ensures C.last == old(C.last)[x := last];
    ensures C.next[x] != null ==> Br == (old(Br)[x := true])[C.next[x] := true];
    ensures C.next[x] == null ==> Br == old(Br)[x := true];

procedure Set_len(x: Ref, len: int);
    requires x != null;
    modifies Br, C.len;
    ensures C.len == old(C.len)[x := len];
    ensures C.prev[x] != null ==> Br == (old(Br)[x := true])[C.prev[x] := true];
    ensures C.prev[x] == null ==> Br == old(Br)[x := true];

procedure Set_rlen(x: Ref, rlen: int);
    requires x != null;
    modifies Br, C.rlen;
    ensures C.rlen == old(C.rlen)[x := rlen];
    ensures C.next[x] != null ==> Br == (old(Br)[x := true])[C.next[x] := true];
    ensures C.next[x] == null ==> Br == old(Br)[x := true];

procedure Set_keys(x: Ref, keys: KeySet);
    requires x != null;
    modifies Br, C.keys;
    ensures C.keys == old(C.keys)[x := keys];
    ensures C.prev[x] != null ==> Br == (old(Br)[x := true])[C.prev[x] := true];
    ensures C.prev[x] == null ==> Br == old(Br)[x := true];

procedure Set_repr(x: Ref, repr: RefSet);
    requires x != null;
    requires C.last[x] != x || (C.last[x] == x && RefSetsEqual(C.repr[x], EmptyRefSet[x := true]));
    modifies Br, C.repr;
    ensures C.repr == old(C.repr)[x := repr];
    ensures C.prev[x] != null ==> Br == (old(Br)[x := true])[C.prev[x] := true];
    ensures C.prev[x] == null ==> Br == old(Br)[x := true];

procedure AddToLastRepr(x: Ref, node: Ref);
    requires x != null;
    requires C.last[x] == x;
    modifies Br, C.repr;
    ensures C.repr == old(C.repr)[x := (old(C.repr)[x])[node := true]];
    ensures Br == old(Br)[x := true];

procedure AddToLastKeys(x: Ref, k: int);
    requires x != null;
    requires C.last[x] == x;
    modifies Br, C.keys;
    ensures C.keys == old(C.keys)[x := (old(C.keys)[x])[k := true]];
    ensures Br == old(Br)[x := true];

procedure DeleteFromLastRepr(x: Ref, node: Ref);
    requires x != null;
    requires C.last[x] == x && C.next[node] == node && C.prev[node] == node;
    modifies Br, C.repr;
    ensures C.repr == old(C.repr)[x := (old(C.repr)[x])[node := false]];
    ensures Br == old(Br)[x := true];

procedure DeleteFromLastKeys(x: Ref, k: int);
    requires x != null;
    requires C.last[x] == x;
    modifies Br, C.keys;
    ensures C.keys == old(C.keys)[x := (old(C.keys)[x])[k := false]];
    ensures Br == old(Br)[x := true];

// Broken Set Manipulation
procedure IfNotBr_ThenLC(x: Ref);
    ensures x != null && !Br[x] ==> LC(C.k, C.next, C.prev,
                                        C.last, C.len, C.rlen, 
                                        C.keys, C.repr, x);

procedure AssertLCAndRemove(x: Ref);
    modifies Br;
    ensures (x != null && LC(C.k, C.next, C.prev,
                                C.last, C.len, C.rlen, 
                                C.keys, C.repr, x))
                ==> Br == old(Br)[x := false];
    ensures (x == null || !LC(C.k, C.next, C.prev,
                                C.last, C.len, C.rlen, 
                                C.keys, C.repr, x))
                ==> Br == old(Br);

// Framing
function Frame_k(mod_set: RefSet, old_k: [Ref]int, k: [Ref]int) returns ([Ref]int);
function Frame_next(mod_set: RefSet, old_next: [Ref]Ref, next: [Ref]Ref) returns ([Ref]Ref);
function Frame_prev(mod_set: RefSet, old_prev: [Ref]Ref, prev: [Ref]Ref) returns ([Ref]Ref);
function Frame_last(mod_set: RefSet, old_last: [Ref]Ref, last: [Ref]Ref) returns ([Ref]Ref);
function Frame_len(mod_set: RefSet, old_len: [Ref]int, len: [Ref]int) returns ([Ref]int);
function Frame_rlen(mod_set: RefSet, old_rlen: [Ref]int, rlen: [Ref]int) returns ([Ref]int);
function Frame_keys(mod_set: RefSet, old_keys: [Ref]KeySet, keys: [Ref]KeySet) returns ([Ref]KeySet);
function Frame_repr(mod_set: RefSet, old_repr: [Ref]RefSet, repr: [Ref]RefSet) returns ([Ref]RefSet);

function {:inline} Frame_all(
    k: [Ref]int, 
    next: [Ref]Ref,
    prev: [Ref]Ref,
    last: [Ref]Ref,
    len: [Ref]int,
    rlen: [Ref]int,
    keys: [Ref]KeySet,
    repr: [Ref]RefSet,
    oldk: [Ref]int, 
    oldnext: [Ref]Ref,
    oldprev: [Ref]Ref,
    oldlast: [Ref]Ref,
    oldlen: [Ref]int,
    oldrlen: [Ref]int,
    oldkeys: [Ref]KeySet,
    oldrepr: [Ref]RefSet,
    mod_set: RefSet,
    old_alloc: RefSet
) returns (bool) 
{
    k == Frame_k(RefSetUnionF(mod_set, RefSetComF(old_alloc)), oldk, k) 
    && next == Frame_next(RefSetUnionF(mod_set, RefSetComF(old_alloc)), oldnext, next) 
    && prev == Frame_prev(RefSetUnionF(mod_set, RefSetComF(old_alloc)), oldprev, prev)
    && last == Frame_last(RefSetUnionF(mod_set, RefSetComF(old_alloc)), oldlast, last)
    && len == Frame_len(RefSetUnionF(mod_set, RefSetComF(old_alloc)), oldlen, len)
    && rlen == Frame_rlen(RefSetUnionF(mod_set, RefSetComF(old_alloc)), oldrlen, rlen)
    && keys == Frame_keys(RefSetUnionF(mod_set, RefSetComF(old_alloc)), oldkeys, keys)
    && repr == Frame_repr(RefSetUnionF(mod_set, RefSetComF(old_alloc)), oldrepr, repr)
}

// Alloc set reasoning
function {:inline} InAlloc(
    k: [Ref]int, 
    next: [Ref]Ref,
    prev: [Ref]Ref,
    last: [Ref]Ref,
    len: [Ref]int,
    rlen: [Ref]int,
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
    && (last[x] != null ==> alloc[last[x]])
    && RefSetSubset(repr[x], alloc)
  )
}

procedure InAllocParam(x: Ref);
    ensures x != null ==> InAlloc(C.k, C.next, C.prev, 
                                C.last, C.len, C.rlen,
                                C.keys, C.repr, x, alloc);

function {:inline} Fresh(expr: RefSet, newalloc: RefSet, oldalloc: RefSet) returns (bool)
{
    RefSetSubset(expr, newalloc)
    && RefSetsDisjoint(expr, oldalloc)
}

function {:inline} Unchanged(
    k: [Ref]int, 
    next: [Ref]Ref,
    prev: [Ref]Ref,
    last: [Ref]Ref,
    len: [Ref]int,
    rlen: [Ref]int,
    keys: [Ref]KeySet,
    repr: [Ref]RefSet,
    oldk: [Ref]int, 
    oldnext: [Ref]Ref,
    oldprev: [Ref]Ref,
    oldlast: [Ref]Ref,
    oldlen: [Ref]int,
    oldrlen: [Ref]int,
    oldkeys: [Ref]KeySet,
    oldrepr: [Ref]RefSet,
    x: Ref
) returns (bool) 
{
    x != null ==> (
        k[x] == oldk[x]
        && next[x] == oldnext[x]
        && prev[x] == oldprev[x]
        && last[x] == oldlast[x]
        && len[x] == oldlen[x]
        && rlen[x] == oldrlen[x]
        && KeySetsEqual(keys[x], oldkeys[x])
        && RefSetsEqual(repr[x], oldrepr[x])
    )
}
