// Supporting Artifact for
// "Predictable Verification using Intrinsic Definitions of Data Structures"
// by Anonymous Authors.
// 
// Artifact by Anonymous Author, 2023. 
//
// Definition of Circular Lists.

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

function {:inline} Frame_last(mod_set: RefSet, old_last: [Ref]Ref, last: [Ref]Ref) returns ([Ref]Ref)
{
    MapIte_Ref_Ref(mod_set, last, old_last)
}

function {:inline} Frame_len(mod_set: RefSet, old_len: [Ref]int, len: [Ref]int) returns ([Ref]int)
{
    MapIte_Ref_int(mod_set, len, old_len)
}

function {:inline} Frame_rlen(mod_set: RefSet, old_rlen: [Ref]int, rlen: [Ref]int) returns ([Ref]int)
{
    MapIte_Ref_int(mod_set, rlen, old_rlen)
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
