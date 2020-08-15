/*
 * Copyright 2020 ConsenSys AG.
 *
 * Licensed under the Apache License, Version 2.0 (the "License"); you may 
 * not use this file except in compliance with the License. You may obtain 
 * a copy of the License at http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software dis-
 * tributed under the License is distributed on an "AS IS" BASIS, WITHOUT 
 * WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the 
 * License for the specific language governing permissions and limitations 
 * under the License.
 */
 
include "IntTree.dfy"
include "CompleteTrees.dfy"
include "GenericComputation.dfy"
include "Helpers.dfy"
include "MerkleTrees.dfy"
include "NextPathInCompleteTreesLemmas.dfy"
include "PathInCompleteTrees.dfy"
include "SeqOfBits.dfy"
include "Trees2.dfy"

module Foo {
 
    import opened DiffTree
    import opened CompleteTrees
    import opened GenericComputation
    import opened Helpers
    import opened MerkleTrees
    import opened NextPathInCompleteTreesLemmas
    import opened PathInCompleteTrees
    import opened SeqOfBits
    import opened Trees

    /**
     *  If b and b' agree on values at which p[i] == 1 and b has siblings at p[..], then 
     *  b' has siblings at same location.  
     */
    lemma {:induction p, r} siblingsLeft(p : seq<bit>, l : seq<int>, r : Tree<int>, b : seq<int>, b': seq<int>, k : nat) 
        /** Merkle tree. */
        requires height(r) >= 2
        requires |l| == |leavesIn(r)|
        requires isMerkle2(r, l, diff)
        requires hasLeavesIndexedFrom(r, 0)

        /**  all leaves after the k leaf are zero. */
        requires k < |leavesIn(r)|
        requires forall i :: k < i < |l| ==> l[i] == 0

        /** p is the path to k leaf in r. */
        requires |p| == height(r) - 1
        requires nodeAt(p, r) == leavesIn(r)[k]

        requires |b| == |p|
        /** `b` contains values at left siblings on path `p`. */
        requires forall i :: 0 <= i < |b| ==> p[i] == 1 ==> b[i] == siblingAt(p[..i + 1], r).v

        requires |b'| == |b| && forall i :: 0 <= i < |b'| ==> if p[i] == 1 then b'[i] == b[i] else b'[i] == 0 

        ensures forall i :: 0 <= i < |b'| ==> b'[i] == siblingAt(p[..i + 1], r).v
    {
        leavesRightOfNodeAtPathZeroImpliesRightSiblingsOnPathZero(r, l, k, p, 0);   
    }

    /**
     *  Same as computeRootPath but uses default value 0 on 
     *  right sibling to compute value at root.
     *  Compute the value on a path recursively by computing on children first.
     */
    function computeRootPathDiff(p : seq<bit>, b : seq<int>, seed: int) : int
        requires |p| == |b|
        decreases p
    {
        if |p| == 0 then 
            seed
        else 
            var r := computeRootPathDiff(p[1..], b[1..], seed);
            if p[0] == 0 then
                diff(r, 0)
            else 
                diff(b[0], r)
    }

    /**
     *  Restrict computation to path of length >= 1.
     */
     function computeRootPathDiff2(p : seq<bit>, b : seq<int>, seed: int) : int
        requires |p| >= 1
        requires |p| == |b|
        ensures computeRootPathDiff2(p, b, seed) == computeRootPathDiff(p, b, seed)
        decreases p
    {
        if |p| == 1 then 
            computeRootPathDiff(p, b, seed)
        else 
            var r := computeRootPathDiff(p[1..], b[1..], seed);
            if p[0] == 0 then
                diff(r, 0)
            else 
                diff(b[0], r)
    }

    // lemma foo606(p : seq<bit>, b : seq<int>, seed: int)

    /**
     *  Compute computeRootPathDiff by pre-computing the last 
     *  step.
     *  This corresponds to computing the value of the penultimate node on the path
     *  and then use it to compute the value on the prefix path (without the last node).
     */
    lemma {:induction p, b} foo506(p : seq<bit>, b : seq<int>, seed: int) 
        requires 1 <= |p| == |b|
        ensures computeRootPathDiff(p, b, seed) == 
            computeRootPathDiff(
                p[..|p| - 1], b[..|b| - 1], 
                if p[|p| - 1] == 0 then 
                    diff(seed, 0)
                else 
                    diff(b[|b| - 1], seed)
                )
    {
        if |p| == 1 {
            // Thanks Dafny
        } else {
            //  These equalities are used in the sequel
            calc == {   // eq1
                p[1..][..|p[1..]| - 1];
                p[1..|p| - 1];
            }
            calc == {   //  eq2
                b[1..][..|b[1..]| - 1];
                b[1..|b| - 1];
            }
            if p[0] == 0 {
                calc == {
                    computeRootPathDiff(p, b, seed);
                    diff(computeRootPathDiff(p[1..], b[1..], seed), 0);
                    diff(
                        computeRootPathDiff(p[1..][..|p[1..]| - 1], b[1..][..|b[1..]| - 1], 
                        if p[1..][|p[1..]| - 1] == 0 then diff(seed, 0)
                        else diff(b[1..][|b[1..]| - 1], seed)
                        ), 0
                    );
                    //  by eq1, simplify p[1..][..|p[1..]| - 1] and by eq2 b[1..][..|b[1..]| - 1]
                    diff(
                        computeRootPathDiff(p[1..|p| - 1], b[1..|b| - 1], 
                        if p[|p| - 1] == 0 then diff(seed, 0)
                        else diff(b[|b| - 1], seed)
                        ), 0
                    );
                }
            }
            else {  //  p[0] == 1
                calc == {
                    computeRootPathDiff(p, b, seed);
                    diff(b[0], computeRootPathDiff(p[1..], b[1..], seed));
                    diff(
                        b[0],
                        computeRootPathDiff(p[1..][..|p[1..]| - 1], b[1..][..|b[1..]| - 1], 
                        if p[1..][|p[1..]| - 1] == 0 then diff(seed, 0)
                        else diff(b[1..][|b[1..]| - 1], seed)
                        )
                    );
                    //  by eq1, simplify p[1..][..|p[1..]| - 1] and by eq2 b[1..][..|b[1..]| - 1]
                    diff(
                        b[0],
                        computeRootPathDiff(p[1..|p| - 1], b[1..|b| - 1], 
                        if p[|p| - 1] == 0 then diff(seed, 0)
                        else diff(b[|b| - 1], seed)
                        )
                    );
                }            
            }
        }
    }

    /**
     *  Compute root value starting from end of path.
     *  Recursive computation by simplifying the last node i.e.
     *  computing its value and then iterate on the prefix path.
     */
    function computeRootPathDiffUp(p : seq<bit>, b : seq<int>, seed: int) : int
        requires |p| == |b|
        decreases p
    {
     if |p| == 0 then
        seed 
    else 
        if p[|p| - 1] == 0 then
            computeRootPathDiffUp(p[.. |p| - 1], b[..|b| - 1],diff(seed, 0))
        else        
            computeRootPathDiffUp(p[.. |p| - 1], b[..|b| - 1],diff(b[|b| - 1], seed))
    }

    /**
     *  Compute diff root and collect siblings of next path.
     *  
     *  @param  p       The path.
     *  @param  b       The values of the left siblings of nodes on `p`.
     *  @param  seed    The value at nodeAt(p).
     *  @param  v1      The values of the nodes on the path p.
     *  @returns        The value of diff at the root and a vector of values of
     *                  for the left siblins on nextPath(p).
     */
    function computeRootPathDiffAndLeftSiblingsUp(
        p : seq<bit>, b : seq<int>, seed: int, 
        v1: seq<int>) 
            : (int, seq<int>)
        requires |p| == |b| == |v1|
        requires |p| >= 1
        /** The int value result is the same as the one computed by computeRootPathDiffUp. */
        // ensures computeRootPathDiffAndLeftSiblingsUp(p, b, seed, v1).0 == computeRootPathDiff(p, b, seed)
        // ensures 
        ensures computeRootPathDiffAndLeftSiblingsUp(p, b, seed, v1).1 == computeLeftSiblingOnNextPath(p, v1, b)
        
        decreases p
    {
     if |p| == 1 then
        var r := computeRootPathDiff(p, b, seed);
        (r, v1) 
    else 
        if p[|p| - 1] == 0 then
            var r := computeRootPathDiffAndLeftSiblingsUp(
                    p[.. |p| - 1], b[..|b| - 1],  diff(seed, 0), v1[..|p| - 1]);
                        //  could use  p[.. |p| - 1] instead of v1[..|p| - 1]
                    // [diff(seed, 0)] + b
                    (r.0, b[.. |b| - 1] + [v1[|p| - 1 ]])
        else      
            var r :=  computeRootPathDiffAndLeftSiblingsUp(
                    p[.. |p| - 1], b[..|b| - 1], diff(b[|b| - 1], seed), v1[..|p| - 1]);
                    // [0] + b
                    // v2[..|p| - 1]) + [v1[|p| - 1]]
                    // )
                    (r.0, r.1 + [v1[|p| - 1]])
                    //  could use 0 instead of v1[|p| - 1] but need to adjust 
                    //  computeLeftSiblingOnNextPath to match that
    }

    /**
     *  For path of size >= 2, computeRootPathDiffAndLeftSiblingsUp and computeRootPathDiffUp
     *  yield the same result.
     */
    lemma {:induction p, b, seed, v1} foo888(p : seq<bit>, b : seq<int>, seed: int, v1: seq<int>) 
        requires |p| == |b| == |v1|
        requires |p| >= 1
        ensures computeRootPathDiffAndLeftSiblingsUp(p, b, seed, v1).0 == computeRootPathDiffUp(p, b, seed)
        decreases p
    {
        if |p| == 1 {
            //  Thanks Dafny
            calc == {
                computeRootPathDiffAndLeftSiblingsUp(p, b, seed, v1).0;
                computeRootPathDiff(p, b, seed);
                { computeUpEqualsComputeDown(p, b, seed); }
                computeRootPathDiffUp(p, b, seed);
            }
        } else {
            if p[|p| - 1] == 0 {
                calc == {
                    computeRootPathDiffAndLeftSiblingsUp(p, b, seed, v1).0;
                    computeRootPathDiffAndLeftSiblingsUp(
                        p[.. |p| - 1], b[..|b| - 1],  diff(seed, 0), v1[..|p| - 1]).0;
                    { foo888(p[.. |p| - 1], b[..|b| - 1],  diff(seed, 0),v1[..|p| - 1]); }
                    computeRootPathDiffUp(p[.. |p| - 1], b[..|b| - 1], diff(seed, 0));
                    calc {
                        p[|p| - 1] == 0;
                    }
                    computeRootPathDiffUp(p, b, seed);
                }
            } else {
                calc == {
                    computeRootPathDiffAndLeftSiblingsUp(p, b, seed, v1).0 ;
                    computeRootPathDiffAndLeftSiblingsUp(
                    p[.. |p| - 1], b[..|b| - 1], diff(b[|b| - 1], seed), v1[..|p| - 1]).0;
                    { foo888(p[.. |p| - 1], b[..|b| - 1],  diff(seed, 0),v1[..|p| - 1]); }
                    computeRootPathDiffUp(p, b, seed);
                }
            }
        }
    }

    lemma {:induction p, b, seed, v1} foo999(p : seq<bit>, b : seq<int>, seed: int, v1: seq<int>) 
        requires |p| == |b| == |v1|
        requires |p| >= 1
        ensures computeRootPathDiffAndLeftSiblingsUp(p, b, seed, v1).1 == computeLeftSiblingOnNextPath(p, v1, b)
        decreases p
    {
        if |p| == 1 {
            //  Thanks Dafny
        } else {
            if p[|p| - 1] == 0 {
                // calc == {
                //     computeRootPathDiffAndLeftSiblingsUp(p, b, seed, v1).1;
                //     b[.. |b| - 1] + [v1[|p| - 1]];
                //     computeLeftSiblingOnNextPath(p, v1, b);
                // }
            } else {
                // calc == {
                //     computeRootPathDiffAndLeftSiblingsUp(p, b, seed, v1).1 ;
                //     computeRootPathDiffAndLeftSiblingsUp(
                //     p[.. |p| - 1], b[..|b| - 1], diff(b[|b| - 1], seed), v1[..|p| - 1]).1 + [v1[|p| - 1]];
                //     // { foo999(p[.. |p| - 1], b[..|b| - 1],  diff(seed, 0),v1[..|p| - 1]); }
                //     computeLeftSiblingOnNextPath(p, v1, b);
                // }
            }
        }
    }


    /**
     *  Computing up or down yield the same result!
     */
    lemma {:induction p, b, seed} computeUpEqualsComputeDown(p : seq<bit>, b : seq<int>, seed: int) 
        requires |p| == |b|
        ensures computeRootPathDiffUp(p, b, seed) == computeRootPathDiff(p, b, seed)
    {
        if |p| <= 1 {
            //  Thanks Dafny
        } else {    
            //  |p| >= 2
            //  Split on values of p[|p| - 1]
            if p[|p| - 1] == 0 {
                calc == {
                    computeRootPathDiffUp(p, b, seed);
                    computeRootPathDiffUp(p[.. |p| - 1], b[..|b| - 1],diff(seed, 0));
                    //  Induction assumption
                    computeRootPathDiff(p[.. |p| - 1], b[..|b| - 1],diff(seed, 0));
                    { foo506(p, b, seed); }
                    computeRootPathDiff(p, b, seed);
                }
            } else  {
                assert(p[|p| - 1] == 1 );
                calc == {
                    computeRootPathDiffUp(p, b, seed);
                     computeRootPathDiffUp(p[.. |p| - 1], b[..|b| - 1],diff(b[|b| - 1], seed));
                    //  Induction assumption
                    computeRootPathDiff(p[.. |p| - 1], b[..|b| - 1], diff(b[|b| - 1], seed));
                    { foo506(p, b, seed); }
                    computeRootPathDiff(p, b, seed);
                }
            }
        }
    }

    /**
     *  Show that if right sibling values are zero,  computeRootPathDiff
     *  computes the same result as computeRootPath.
     */
    lemma {:induction p} computeRootPathDiffEqualscomputeRootPath(p : seq<bit>, b : seq<int>, seed: int) 
        requires |b| == |p| 
        requires forall i :: 0 <= i < |b| ==> p[i] == 0 ==> b[i] == 0
        ensures computeRootPathDiff(p, b, seed) == computeRootPath(p, b, diff, seed)
        decreases p
    {
        if |p| == 0 {
            //  Thanks Dafny
        } else {
            //  Compute result on suffixes p[1..], b[1..]
            var r := computeRootPathDiff(p[1..], b[1..], seed);
            var r' := computeRootPath(p[1..], b[1..], diff, seed);

            //  Use inductive assumption on p[1..], b[1..]
            computeRootPathDiffEqualscomputeRootPath(p[1..], b[1..], seed);
            // HI implies r == r'
            
            calc == {   //  These terms are equal
                computeRootPathDiff(p, b, seed) ;
                if p[0] == 0 then diff(r, 0) else  diff(b[0], r);
                if p[0] == 0 then diff(r', 0) else  diff(b[0], r');
                computeRootPath(p, b, diff, seed);
            }
        }
    }

    /**
     *  When two vectors b and b' have the same values for i such that p[i] == 1,
     *  i.e. for every left sibling b and b' coincide, then 
     *  computeRootPathDiff(p, b, seed) == computeRootPathDiff(p, b', seed)
     */
    lemma {:induction p} sameComputeDiffPath(p : seq<bit>, b : seq<int>, b': seq<int>, seed: int)
        requires |b| == |p| == |b'|
        requires forall i :: 0 <= i < |b| ==> p[i] == 1 ==> b[i] == b'[i]
        ensures computeRootPathDiff(p, b, seed) == computeRootPathDiff(p, b', seed)
        decreases p 
    {
        if |p| == 0 {
            //
        } else {
            var r := computeRootPathDiff(p[1..], b[1..], seed);
            var r' := computeRootPathDiff(p[1..], b'[1..], seed);
            if p[0] == 0 {
                calc == {
                    computeRootPathDiff(p, b, seed) ;
                    diff(r, 0) ;
                    // Induction on p[1..], b[1..], b'[1..], seed
                    { sameComputeDiffPath(p[1..], b[1..], b'[1..], seed); }  
                    diff(r', 0);
                    computeRootPathDiff(p, b', seed);
                }
            } else {
                calc == {
                    computeRootPathDiff(p, b, seed) ;
                    diff(b[0], r) ;
                    // Induction on p[1..], b[1..], b'[1..], seed
                    { sameComputeDiffPath(p[1..], b[1..], b'[1..], seed); }  
                    diff(b'[0], r');
                    computeRootPathDiff(p, b', seed);
                }
            }
        }
    }

    function makeB(p: seq<bit>, b: seq<int>) : seq<int> 
        requires |p| == |b|
        decreases p
        ensures |makeB(p, b)| == |b| && forall i :: 0 <= i < |b| ==> if p[i] == 1 then makeB(p,b)[i] == b[i] else makeB(p, b)[i] == 0 
    {
        if |p| == 0 then
            []
        else    
            [if p[0] == 0 then 0 else b[0]] + makeB(p[1..], b[1..])
    }

    /**
     *  Weakening of computeOnPathYieldsRootValue, requesting values on left siblings only, when
     *  merkle tree and path is not last non-null leaf.
     */
     lemma {:induction p, r, b} computeOnPathYieldsRootValueDiff(p : seq<bit>, l : seq<int>, r : Tree<int>, b : seq<int>, k : nat) 
        /** Merkle tree. */
        requires height(r) >= 2
        requires |l| == |leavesIn(r)|
        requires isMerkle2(r, l, diff)
        requires hasLeavesIndexedFrom(r, 0)

        /**  all leaves after the k leaf are zero. */
        requires k < |leavesIn(r)|
        requires forall i :: k < i < |l| ==> l[i] == 0

        /** p is the path to k leaf in r. */
        requires |p| == height(r) - 1
        requires nodeAt(p, r) == leavesIn(r)[k]

        requires |b| == |p|
        /** `b` contains values at left siblings on path `p`. */
        requires forall i :: 0 <= i < |b| ==> p[i] == 1 ==> b[i] == siblingAt(p[..i + 1], r).v

        ensures r.v == computeRootPathDiff(p, b, leavesIn(r)[k].v)

        decreases r
    {

        //  define a new seq b' that holds default values for right siblings
        //  and prove that pre-conditions of computeOnPathYieldsRootValue hold.

        // var b' : seq<int> :| |b'| == |b| && forall i :: 0 <= i < |b| ==> if p[i] == 1 then b'[i] == b[i] else b'[i] == 0 ; 
        var b' := makeB(p, b);

        leavesRightOfNodeAtPathZeroImpliesRightSiblingsOnPathZero(r, l, k, p, 0);
        assert(forall i :: 0 <= i < |p| ==> 
            p[i] == 0 ==> siblingAt(p[..i + 1], r).v == 0);

        siblingsLeft(p, l, r, b, b', k);
        assert(forall i :: 0 <= i < |p| ==> b'[i] == siblingAt(p[..i + 1], r).v);

        assert(forall i :: 0 <= i < |p| ==> p[i] == 0 ==> b'[i] == 0);

        computeOnPathYieldsRootValue(p, r, b', diff, leavesIn(r)[k].v);
        assert(computeRootPath(p, b', diff, leavesIn(r)[k].v) ==  r.v);
        computeRootPathDiffEqualscomputeRootPath(p, b', leavesIn(r)[k].v);
        assert(computeRootPathDiff(p, b',  leavesIn(r)[k].v) == computeRootPath(p, b', diff,  leavesIn(r)[k].v));

        sameComputeDiffPath(p, b, b', leavesIn(r)[k].v);
    }

    /**
     *  Main function to compute the root value.
     */
     function computeRootDiffUp(p : seq<bit>, l : seq<int>, r : Tree<int>, b : seq<int>, k : nat) : int
        /** Merkle tree. */
        requires height(r) >= 2
        requires |l| == |leavesIn(r)|
        requires isMerkle2(r, l, diff)
        requires hasLeavesIndexedFrom(r, 0)

        /**  all leaves after the k leaf are zero. */
        requires k < |leavesIn(r)|
        requires forall i :: k < i < |l| ==> l[i] == 0

        /** p is the path to k leaf in r. */
        requires |p| == height(r) - 1
        requires nodeAt(p, r) == leavesIn(r)[k]

        requires |b| == |p|
        /** `b` contains values at left siblings on path `p`. */
        requires forall i :: 0 <= i < |b| ==> p[i] == 1 ==> b[i] == siblingAt(p[..i + 1], r).v

        ensures r.v == computeRootDiffUp(p, l, r, b, k)
    {
        //  Values on left sibling are enough to compuute r.v using computeRootPathDiff
        computeOnPathYieldsRootValueDiff(p, l, r, b, k);
        //  Compute computeRootUp yields same value as computeRootPathDiff
        computeUpEqualsComputeDown(p, b, leavesIn(r)[k].v);
        computeRootPathDiffUp(p, b, leavesIn(r)[k].v)
    }


    function incMerkle(p: seq<bit>, l : seq<int>, r : Tree<int>, b : seq<int>, k : nat) : (int, seq<int>) 

        requires height(r) >= 2
        requires  isCompleteTree(r)
        requires hasLeavesIndexedFrom(r, 0)

        requires |l| == |leavesIn(r)|
        requires k < |leavesIn(r)| - 1
        requires forall i :: k < i < |l| ==> l[i] == 0

        requires k < power2(height(r) - 1) 
        requires |b| == |p|
        requires isMerkle2(r, l, diff)

        requires p == natToBitList(k, height(r) - 1)
        requires forall i :: 0 <= i < |b| ==> p[i] == 1 ==> b[i] == siblingAt(p[..i + 1], r).v

        ensures r.v == incMerkle(p, l, r, b, k).0
    {
        // var p := natToBitList(k, height(r) - 1);
        assert(|p| == height(r) - 1);
        indexOfLeafisIntValueOfPath(p, r,k);
        // foo200(natToBitList(k, height(r) - 1), r, k);
        // bitToNatToBitsIsIdentity();
         bitToNatToBitsIsIdentity(k, height(r) - 1);
        // assert(bitListToNat);
        // assert(nodeAt(p, r) == leavesIn(r)[k]);
         indexOfLeafisIntValueOfPath(p, r, k);
        assert(bitListToNat(p) == k ==> nodeAt(p, r) == leavesIn(r)[k]);
        assert(nodeAt(p, r) == leavesIn(r)[k]);

        (computeRootDiffUp(p, l, r, b, k), [])
    }


 }