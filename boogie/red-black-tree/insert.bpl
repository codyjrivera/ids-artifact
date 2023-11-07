// Supporting Artifact for
// "Predictive Verification using Intrinsic Definitions of Data Structures"
// by Adithya Murali, Cody Rivera, and P. Madhusudan.
// 
// Artifact by Cody Rivera, 2023. 
//
// Verification of Red-Black Tree Insert.

procedure RBTInsertContract(x: Ref, k: int)
    returns (ret: Ref);
    requires Br == EmptyRefSet;
    requires x != null ==> LC(C.k, C.l, C.r, C.p, 
                              C.min, C.max, C.keys,
                              C.repr, C.black, C.black_height, 
                              x, alloc);
    requires x != null ==> !(C.keys[x])[k];
    modifies C.k, C.l, C.r, C.p, 
        C.min, C.max, C.keys,
        C.repr, C.black, C.black_height, Br, alloc;
    ensures RefSetSubset(old(alloc), alloc);
    ensures ret != null;
    ensures (LC(C.k, C.l, C.r, C.p, 
               C.min, C.max, C.keys,
               C.repr, C.black, C.black_height, 
               ret, alloc) ||
             LC_Trans_RedRed(C.k, C.l, C.r, C.p, 
               C.min, C.max, C.keys,
               C.repr, C.black, C.black_height, 
               ret, alloc));
    ensures C.p[ret] == null;
    ensures x != null && x != ret ==> C.p[x] != old(C.p)[x];
    ensures (x == null ==>
                KeySetsEqual(C.keys[ret], EmptyKeySet[k := true])
                && C.min[ret] == k
                && C.max[ret] == k
                && C.black_height[ret] == 0
                && fresh(C.repr[ret], alloc, old(alloc))
                && RefSetSubset(Br, EmptyRefSet[ret := true]));
    ensures (x != null ==>
                KeySetsEqual(C.keys[ret], (old(C.keys)[x])[k := true])
                && (C.min[ret] == old(C.min)[x] || C.min[ret] == k)
                && (C.max[ret] == old(C.max)[x] || C.max[ret] == k)
                && C.black_height[ret] == old(C.black_height)[x]
                && (C.black[ret] ||
                        (!C.black[ret] && ((C.l[ret] == null || C.black[C.l[ret]] || C.r[ret] == null || C.black[C.r[ret]])
                        && (!old(C.black)[x] || ((C.l[ret] == null || C.black[C.l[ret]]) && (C.r[ret] == null || C.black[C.r[ret]]))))))
                && fresh(RefSetDiffF(C.repr[ret], old(C.repr)[x]), alloc, old(alloc))
                && (old(C.p)[x] == null ==> RefSetSubset(Br, EmptyRefSet[ret := true]))
                && (old(C.p)[x] != null ==> RefSetSubset(Br, (EmptyRefSet[ret := true])[old(C.p)[x] := true])));