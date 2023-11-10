// Supporting Artifact for
// "Predictive Verification using Intrinsic Definitions of Data Structures"
// by Adithya Murali, Cody Rivera, and P. Madhusudan.
// 
// Artifact by Cody Rivera, 2023. 
//
// Verification of Red-Black Tree Delete, left fixup procedure.

function {:inline} GetBlackHeight(black_height: [Ref]int, x: Ref) returns (int)
{
    if x == null then 0 else black_height[x]
}

function {:inline} MaxInt(x: int, y: int) returns (int)
{
    if x > y then x else y
}

procedure RBTDeleteLeftFixupContract(x: Ref) 
    returns (ret: Ref, fixed: bool);
    requires x != null;
    requires RefSetsDisjoint(Br, (C.repr[x])[x := false]);
    requires LC_Trans_DoubleBlack(C.k, C.l, C.r, C.p, 
                C.min, C.max, C.keys,
                C.repr, C.black, C.black_height, 
                x);
    requires (C.l[x] == null && C.r[x] != null && C.black_height[C.r[x]] == 1)
            || (C.l[x] != null && C.r[x] != null && C.black_height[C.l[x]] + 1 == C.black_height[C.r[x]]);
    requires (C.l[x] == null || C.black[C.l[x]]);
    requires (C.black[x] || (C.r[x] == null || C.black[C.r[x]]));
    modifies C.k, C.l, C.r, C.p, 
                C.min, C.max, C.keys,
                C.repr, C.black, C.black_height;
    ensures ret != null;
    ensures x != ret ==> (
        C.p[x] != old(C.p)[x]
        && !(C.repr[ret])[C.p[x]]
        && (C.l[x] != null ==> (C.repr[ret])[C.l[x]])
        && (C.r[x] != null ==> (C.repr[ret])[C.r[x]])
    );
    ensures LC(C.k, C.l, C.r, C.p, 
                C.min, C.max, C.keys,
                C.repr, C.black, C.black_height, 
                ret);
    ensures C.p[ret] == null;
    ensures KeySetsEqual(C.keys[ret], old(C.keys)[x]);
    ensures C.min[ret] == old(C.min)[x];
    ensures C.max[ret] == old(C.max)[x];
    ensures RefSetsEqual(C.repr[ret], old(C.repr)[x]);
    ensures C.black[ret] || (!C.black[ret] && !old(C.black)[x]);
    ensures (fixed && C.black_height[ret] == old(C.black_height)[x])
            ||  (!fixed && old(C.black)[x] && C.black_height[ret] == old(C.black_height)[x] - 1);
    ensures old(C.p)[x] == null ==> RefSetsEqual(Br, old(Br)[x := false]);
    ensures old(C.p)[x] != null ==> RefSetsEqual(Br, (old(Br)[x := false])[old(C.p)[x] := true]);
    // Framing conditions.
    ensures Frame_all(
        C.k, C.l, C.r, C.p, 
        C.min, C.max, C.keys,
        C.repr, C.black, C.black_height,
        old(C.k), old(C.l), old(C.r), old(C.p), 
        old(C.min), old(C.max), old(C.keys),
        old(C.repr), old(C.black), old(C.black_height),
        old(C.repr)[x], old(alloc)
    );

procedure RBTDeleteLeftFixup(x: Ref) 
    returns (ret: Ref, fixed: bool)
    requires x != null;
    requires RefSetsDisjoint(Br, (C.repr[x])[x := false]);
    requires LC_Trans_DoubleBlack(C.k, C.l, C.r, C.p, 
                C.min, C.max, C.keys,
                C.repr, C.black, C.black_height, 
                x);
    requires (C.l[x] == null && C.r[x] != null && C.black_height[C.r[x]] == 1)
            || (C.l[x] != null && C.r[x] != null && C.black_height[C.l[x]] + 1 == C.black_height[C.r[x]]);
    requires (C.l[x] == null || C.black[C.l[x]]);
    requires (C.black[x] || (C.r[x] == null || C.black[C.r[x]]));
    modifies C.k, C.l, C.r, C.p, 
                C.min, C.max, C.keys,
                C.repr, C.black, C.black_height;
    ensures ret != null;
    ensures x != ret ==> (
        C.p[x] != old(C.p)[x]
        && !(C.repr[ret])[C.p[x]]
        && (C.l[x] != null ==> (C.repr[ret])[C.l[x]])
        && (C.r[x] != null ==> (C.repr[ret])[C.r[x]])
    );
    ensures LC(C.k, C.l, C.r, C.p, 
                C.min, C.max, C.keys,
                C.repr, C.black, C.black_height, 
                ret);
    ensures C.p[ret] == null;
    ensures KeySetsEqual(C.keys[ret], old(C.keys)[x]);
    ensures C.min[ret] == old(C.min)[x];
    ensures C.max[ret] == old(C.max)[x];
    ensures RefSetsEqual(C.repr[ret], old(C.repr)[x]);
    ensures C.black[ret] || (!C.black[ret] && !old(C.black)[x]);
    ensures (fixed && C.black_height[ret] == old(C.black_height)[x])
            ||  (!fixed && old(C.black)[x] && C.black_height[ret] == old(C.black_height)[x] - 1);
    ensures old(C.p)[x] == null ==> RefSetsEqual(Br, old(Br)[x := false]);
    ensures old(C.p)[x] != null ==> RefSetsEqual(Br, (old(Br)[x := false])[old(C.p)[x] := true]);
    // Framing conditions.
    ensures Frame_all(
        C.k, C.l, C.r, C.p, 
        C.min, C.max, C.keys,
        C.repr, C.black, C.black_height,
        old(C.k), old(C.l), old(C.r), old(C.p), 
        old(C.min), old(C.max), old(C.keys),
        old(C.repr), old(C.black), old(C.black_height),
        old(C.repr)[x], old(alloc)
    );
{
    // Local variable declarations
    var xl: Ref;
    var xr: Ref;
    var p: Ref;
    var xrl: Ref;
    var xrr: Ref;
    var xrll: Ref;
    var xrlr: Ref;
    var oldxblack: bool;
    var bh: int;
    
    // Intermediate Expresssions

    

    call InAllocParam(x);

    call xl := Get_l(x);
    call xr := Get_r(x);

    call IfNotBr_ThenLC(xl);
    call IfNotBr_ThenLC(xr);

    call xr_black := Get_black(xr);
    if (xr != null && !xr_black) {
        
    } else {
        assume false;
    }


    assume false;
}
