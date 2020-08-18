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

include "IncAlgoV1.dfy"
include "CompleteTrees.dfy"
include "ComputeRootPath.dfy"
include "GenericComputation.dfy"
include "Helpers.dfy"
include "MerkleTrees.dfy"
include "NextPathInCompleteTreesLemmas.dfy"
include "PathInCompleteTrees.dfy"
include "SeqOfBits.dfy"
include "Trees2.dfy"

module IncAlgoV2 {
 
    import opened DiffTree
    import opened IncAlgoV1
    import opened CompleteTrees
    import opened ComputeRootPath
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
    // lemma {:induction p, r} siblingsLeft(p : seq<bit>, r : Tree<int>, b : seq<int>, b': seq<int>, k : nat) 

    //     requires isCompleteTree(r)
    //     /** `r` is decorated with attribute `f`. */
    //     requires isDecoratedWith(diff, r)
    //     requires height(r) >= 2

    //     /**  all leaves after the k leaf are zero. */
    //     requires k < |leavesIn(r)|
    //     requires forall i :: k < i < |leavesIn(r)| ==> leavesIn(r)[i].v == 0

    //     /** p is the path to k leaf in r. */
    //     requires hasLeavesIndexedFrom(r, 0)
    //     requires |p| == height(r) - 1
    //     requires nodeAt(p, r) == leavesIn(r)[k]

    //     requires |b| == |p|
    //     /** `b` contains values at left siblings on path `p`. */
    //     requires forall i :: 0 <= i < |b| ==> p[i] == 1 ==> b[i] == siblingAt(p[..i + 1], r).v

    //     /** B abd b' agree on values at indices where p[i] == 1, and otherwise b'[i] == 0 */
    //     requires |b'| == |b| && forall i :: 0 <= i < |b'| ==> if p[i] == 1 then b'[i] == b[i] else b'[i] == 0 

    //     ensures forall i :: 0 <= i < |b'| ==> b'[i] == siblingAt(p[..i + 1], r).v
    // {
    //     leavesRightOfNodeAtPathZeroImpliesRightSiblingsOnPathZero(r, k, p, 0);   
    // }

    /**
     *  Same as computeRootPath but uses default value 0 on 
     *  right sibling to compute value at root.
     *  Compute the value on a path recursively by computing on children first.
     */
    // function computeRootPathDiff(p : seq<bit>, b : seq<int>, seed: int) : int
    //     requires |p| == |b|
    //     decreases p
    // {
    //     if |p| == 0 then 
    //         seed
    //     else 
    //         var r := computeRootPathDiff(p[1..], b[1..], seed);
    //         if p[0] == 0 then
    //             diff(r, 0)
    //         else 
    //             diff(b[0], r)
    // }

    /**
     *  Restrict computation to path of length >= 1.
     */
    //  function computeRootPathDiff2(p : seq<bit>, b : seq<int>, seed: int) : int
    //     requires |p| >= 1
    //     requires |p| == |b|
    //     ensures computeRootPathDiff2(p, b, seed) == computeRootPathDiff(p, b, seed)
    //     decreases p
    // {
    //     if |p| == 1 then 
    //         computeRootPathDiff(p, b, seed)
    //     else 
    //         var r := computeRootPathDiff(p[1..], b[1..], seed);
    //         if p[0] == 0 then
    //             diff(r, 0)
    //         else 
    //             diff(b[0], r)
    // }

    // lemma foo606(p : seq<bit>, b : seq<int>, seed: int)

    /**
     *  Compute computeRootPathDiff by pre-computing the last 
     *  step.
     *  This corresponds to computing the value of the penultimate node on the path
     *  and then use it to compute the value on the prefix path (without the last node).
     */
    // lemma {:induction p, b} foo506(p : seq<bit>, b : seq<int>, seed: int) 
    //     requires 1 <= |p| == |b|
    //     ensures computeRootPathDiff(p, b, seed) == 
    //         computeRootPathDiff(
    //             p[..|p| - 1], b[..|b| - 1], 
    //             if p[|p| - 1] == 0 then 
    //                 diff(seed, 0)
    //             else 
    //                 diff(b[|b| - 1], seed)
    //             )
    // {
    //     if |p| == 1 {
    //         // Thanks Dafny
    //     } else {
    //         //  These equalities are used in the sequel
    //         calc == {   // eq1
    //             p[1..][..|p[1..]| - 1];
    //             p[1..|p| - 1];
    //         }
    //         calc == {   //  eq2
    //             b[1..][..|b[1..]| - 1];
    //             b[1..|b| - 1];
    //         }
    //         if p[0] == 0 {
    //             calc == {
    //                 computeRootPathDiff(p, b, seed);
    //                 diff(computeRootPathDiff(p[1..], b[1..], seed), 0);
    //                 diff(
    //                     computeRootPathDiff(p[1..][..|p[1..]| - 1], b[1..][..|b[1..]| - 1], 
    //                     if p[1..][|p[1..]| - 1] == 0 then diff(seed, 0)
    //                     else diff(b[1..][|b[1..]| - 1], seed)
    //                     ), 0
    //                 );
    //                 //  by eq1, simplify p[1..][..|p[1..]| - 1] and by eq2 b[1..][..|b[1..]| - 1]
    //                 diff(
    //                     computeRootPathDiff(p[1..|p| - 1], b[1..|b| - 1], 
    //                     if p[|p| - 1] == 0 then diff(seed, 0)
    //                     else diff(b[|b| - 1], seed)
    //                     ), 0
    //                 );
    //             }
    //         }
    //         else {  //  p[0] == 1
    //             calc == {
    //                 computeRootPathDiff(p, b, seed);
    //                 diff(b[0], computeRootPathDiff(p[1..], b[1..], seed));
    //                 diff(
    //                     b[0],
    //                     computeRootPathDiff(p[1..][..|p[1..]| - 1], b[1..][..|b[1..]| - 1], 
    //                     if p[1..][|p[1..]| - 1] == 0 then diff(seed, 0)
    //                     else diff(b[1..][|b[1..]| - 1], seed)
    //                     )
    //                 );
    //                 //  by eq1, simplify p[1..][..|p[1..]| - 1] and by eq2 b[1..][..|b[1..]| - 1]
    //                 diff(
    //                     b[0],
    //                     computeRootPathDiff(p[1..|p| - 1], b[1..|b| - 1], 
    //                     if p[|p| - 1] == 0 then diff(seed, 0)
    //                     else diff(b[|b| - 1], seed)
    //                     )
    //                 );
    //             }            
    //         }
    //     }
    // }

    /**
     *  Compute root value starting from end of path.
     *  Recursive computation by simplifying the last node i.e.
     *  computing its value and then iterate on the prefix path.
     */
    // function computeRootPathDiffUp(p : seq<bit>, b : seq<int>, seed: int) : int
    //     requires |p| == |b|
    //     decreases p
    // {
    //  if |p| == 0 then
    //     seed 
    // else 
    //     if p[|p| - 1] == 0 then
    //         computeRootPathDiffUp(p[.. |p| - 1], b[..|b| - 1],diff(seed, 0))
    //     else        
    //         computeRootPathDiffUp(p[.. |p| - 1], b[..|b| - 1],diff(b[|b| - 1], seed))
    // }

    /**
     *  Collect all the diff values computed on the path p.
     */
    // function computeAllPathDiffUp(p : seq<bit>, b : seq<int>, seed: int) : seq<int>
    //     requires |p| == |b|
    //     ensures |computeAllPathDiffUp(p, b, seed)| == |p| 
    //     decreases p
    // {
    //  if |p| == 0 then
    //     [] 
    // else 
    //     if p[|p| - 1] == 0 then
    //         computeAllPathDiffUp(p[.. |p| - 1], b[..|b| - 1],diff(seed, 0)) + [seed]
    //     else        
    //         computeAllPathDiffUp(p[.. |p| - 1], b[..|b| - 1],diff(b[|b| - 1], seed)) + [seed]
    // }

    /**
     *  The sequence collected by computeAllPathDiffUp corresponds to the sequence
     *  of values computed by computeRootPathDiffUp on suffixes.
     */
    // lemma computeAllDiffUpPrefixes(p : seq<bit>, b : seq<int>, seed: int)
    //     requires |p| == |b|
    //     ensures forall i :: 0 <= i < |computeAllPathDiffUp(p, b, seed)| ==>
    //         computeAllPathDiffUp(p, b, seed)[i] == computeRootPathDiffUp(p[i + 1..], b[i + 1..], seed) 
    // {
    //     if |p| == 0 {
    //         //  Thanks Dafny.
    //     } else {
    //         forall ( i : nat | 0 <= i < |p|)
    //             ensures computeAllPathDiffUp(p, b, seed)[i] == computeRootPathDiffUp(p[i + 1..], b[i + 1..], seed) 
    //         {
    //             if p[|p| - 1] == 0 {
    //                 if i < |p| - 1 {
    //                     calc == {
    //                         computeRootPathDiffUp(p, b, seed);
    //                         computeRootPathDiffUp(p[.. |p| - 1], b[..|b| - 1],diff(seed, 0));
    //                     }
    //                     var a := computeAllPathDiffUp(p[.. |p| - 1], b[..|b| - 1],diff(seed, 0)) + [diff(seed, 0)];
    //                     // var b := 
    //                     calc == {
    //                         computeAllPathDiffUp(p, b, seed)[i];
    //                         a[i];
    //                         { computeAllDiffUpPrefixes(p[.. |p| - 1], b[.. |p| - 1],diff(seed, 0)); }
    //                         computeRootPathDiffUp(p[.. |p| - 1][i + 1..], b[.. |p| - 1][i + 1..], diff(seed, 0)); 
    //                         calc == {
    //                             p[i + 1..][.. |p[i + 1..]| - 1];
    //                             p[..|p| - 1][i + 1..];
    //                         }   
    //                         computeRootPathDiffUp(p[i + 1..][.. |p[i + 1..]| - 1], b[.. |p| - 1][i + 1..], diff(seed, 0));
    //                         calc == {
    //                             b[i + 1..][.. |p[i + 1..]| - 1];
    //                             b[..|p| - 1][i + 1..];
    //                         }  
    //                         computeRootPathDiffUp(p[i + 1..][.. |p[i + 1..]| - 1], b[i + 1..][.. |p[i + 1..]| - 1], diff(seed, 0));
    //                         computeRootPathDiffUp(p[i + 1..], b[i + 1..], seed) ;
    //                     }
    //                 } else {
    //                     //   i == |p| - 1
    //                 }
    //             } else {
    //                 //  p{|p| - 1} == 1, same as p{|p| - 1} == 1 except that diff(seed, 0) is
    //                 //  replaced by diff(b[|b| - 1], seed)
    //                 if i < |p| - 1 {
    //                     calc == {
    //                         computeRootPathDiffUp(p, b, seed);
    //                         computeRootPathDiffUp(p[.. |p| - 1], b[..|b| - 1],diff(b[|b| - 1], seed));
    //                     }
    //                     var a := computeAllPathDiffUp(p[.. |p| - 1], b[..|b| - 1],diff(b[|b| - 1], seed)) + [diff(b[|b| - 1], seed)];
    //                     // var b := 
    //                     calc == {
    //                         computeAllPathDiffUp(p, b, seed)[i];
    //                         a[i];
    //                         { computeAllDiffUpPrefixes(p[.. |p| - 1], b[.. |p| - 1],diff(b[|b| - 1], seed)); }
    //                         computeRootPathDiffUp(p[.. |p| - 1][i + 1..], b[.. |p| - 1][i + 1..], diff(b[|b| - 1], seed)); 
    //                         calc == {
    //                             p[i + 1..][.. |p[i + 1..]| - 1];
    //                             p[..|p| - 1][i + 1..];
    //                         }   
    //                         computeRootPathDiffUp(p[i + 1..][.. |p[i + 1..]| - 1], b[.. |p| - 1][i + 1..], diff(b[|b| - 1], seed));
    //                         calc == {
    //                             b[i + 1..][.. |p[i + 1..]| - 1];
    //                             b[..|p| - 1][i + 1..];
    //                         }  
    //                         computeRootPathDiffUp(p[i + 1..][.. |p[i + 1..]| - 1], b[i + 1..][.. |p[i + 1..]| - 1],diff(b[|b| - 1], seed));
    //                         computeRootPathDiffUp(p[i + 1..], b[i + 1..], seed) ;
    //                     }
    //                 } else {
    //                     //   i == |p| - 1
    //                 }
    //             }
    //         }
    //     }
    // }

    /**
     *  Compute diff root and collect siblings of next path.
     *  
     *  @param  p           The path.
     *  @param  valOnLeftAt The values of the left siblings of nodes on `p`.
     *  @param  seed        The value at nodeAt(p).
     *  @param  valOnPAt    The values of the nodes on the path p.
     *  @returns            The value of diff at the root and a vector of values of
     *                      for the left siblings on nextPath(p).
     */
    // function computeRootPathDiffAndLeftSiblingsUp(
    //     p : seq<bit>, valOnLeftAt : seq<int>, seed: int, valOnPAt: seq<int>) : (int, seq<int>)
    //     requires |p| == |valOnLeftAt| == |valOnPAt|
    //     requires |p| >= 1
    //     /** This post-condition follows easily from the defs of the functions.
    //      *  The fact that computeRootPathDiffAndLeftSiblingsUp.0 is the same as
    //      *  computeRootPathDiff requires some hints and is proved in computeRootAnSiblingsIsCorrect.
    //      */
    //     ensures computeRootPathDiffAndLeftSiblingsUp(p, valOnLeftAt, seed, valOnPAt).1 == computeLeftSiblingOnNextPath(p, valOnPAt, valOnLeftAt)
        
    //     decreases p
    // {
    //  if |p| == 1 then
    //     var r := computeRootPathDiff(p, valOnLeftAt, seed);
    //     //  if p[0] == 0, the left sibling of nextpath is at p[0] and the value is valOnP
    //     //  Otherise, if p[0] == 1, the sibling for nextPath at this level is a right sibling and
    //     //  we do not care about the value of the second component.
    //     (r, valOnPAt) 
    // else 
    //     if p[|p| - 1] == 0 then
    //         var r := computeRootPathDiffAndLeftSiblingsUp(
    //                 p[.. |p| - 1], valOnLeftAt[..|valOnLeftAt| - 1],  diff(seed, 0), valOnPAt[..|p| - 1]);
    //                     //  could use  p[.. |p| - 1] instead of valOnPAt[..|p| - 1]
    //                 (r.0, valOnLeftAt[.. |valOnLeftAt| - 1] + [valOnPAt[|p| - 1]])
    //     else      
    //         var r :=  computeRootPathDiffAndLeftSiblingsUp(
    //                 p[.. |p| - 1], valOnLeftAt[..|valOnLeftAt| - 1], diff(valOnLeftAt[|valOnLeftAt| - 1], seed), valOnPAt[..|p| - 1]);
    //                 (r.0, r.1 + [valOnPAt[|p| - 1]])
    //                 //  could use 0 instead of v1[|p| - 1] but need to adjust 
    //                 //  computeLeftSiblingOnNextPath to match that
    // }

    /**
     *  Compute the root value and the left siblings concurrently.
     *  The fact that this version and the non-optimised
     *  computeRootPathDiffAndLeftSiblingsUp computes the same result os
     *  provided by lemma v1Equalsv2.
     */
     function computeRootPathDiffAndLeftSiblingsUpv2(
        p : seq<bit>, valOnLeftAt : seq<int>, seed: int) : (int, seq<int>)
        requires |p| == |valOnLeftAt| 
        requires |p| >= 1
       
        decreases p
    {
     if |p| == 1 then
        var r := computeRootPathDiff(p, valOnLeftAt, seed);
        (r, [seed]) 
    else 
        if p[|p| - 1] == 0 then
            var r := computeRootPathDiffAndLeftSiblingsUpv2(
                        p[.. |p| - 1], 
                        valOnLeftAt[..|valOnLeftAt| - 1],   
                        diff(seed, 0) );
                        //  could use  p[.. |p| - 1] instead of valOnPAt[..|p| - 1]
                    (r.0, valOnLeftAt[.. |valOnLeftAt| - 1] + [seed])
        else      
            var r :=  computeRootPathDiffAndLeftSiblingsUpv2(
                    p[.. |p| - 1], 
                    valOnLeftAt[..|valOnLeftAt| - 1],  
                    diff(valOnLeftAt[|valOnLeftAt| - 1], seed));
                    (r.0, r.1 + [seed])
                    //  could use 0 instead of v1[|p| - 1] but need to adjust 
                    //  computeLeftSiblingOnNextPath to match that
    }

    /**
     *  For path of size >= 2, computeRootPathDiffAndLeftSiblingsUp and computeRootPathDiffUp
     *  yield the same result.
     */
    // lemma {:induction p, b, seed, v1} computeRootAndSiblingsIsCorrect(p : seq<bit>, b : seq<int>, seed: int, v1: seq<int>) 
    //     requires |p| == |b| == |v1|
    //     requires |p| >= 1
    //     /** We prove the following property: */
    //     ensures computeRootPathDiffAndLeftSiblingsUp(p, b, seed, v1).0 == computeRootPathDiffUp(p, b, seed) 
    //     /** And with the post condition of computeRootPathDiffAndLeftSiblingsUp 
    //      *  it gives the following general result: if the returned value is (r, xs)
    //      *  1. then r is the same as computeRootPathDiffUp
    //      *  2. xs is the the same as the computeLeftSiblingOnNextPath(p)
    //      */
    //     ensures  computeRootPathDiffAndLeftSiblingsUp(p, b, seed, v1) == 
    //         (computeRootPathDiffUp(p, b, seed),
    //         computeLeftSiblingOnNextPath(p, v1, b)
    //         )
    //     decreases p
    // {
    //     if |p| == 1 {
    //         //  Thanks Dafny
    //         calc == {
    //             computeRootPathDiffAndLeftSiblingsUp(p, b, seed, v1).0;
    //             computeRootPathDiff(p, b, seed);
    //             { computeUpEqualsComputeDown(p, b, seed); }
    //             computeRootPathDiffUp(p, b, seed);
    //         }
    //     } else {
    //         if p[|p| - 1] == 0 {
    //             calc == {
    //                 computeRootPathDiffAndLeftSiblingsUp(p, b, seed, v1).0;
    //                 computeRootPathDiffAndLeftSiblingsUp(
    //                     p[.. |p| - 1], b[..|b| - 1],  diff(seed, 0), v1[..|p| - 1]).0;
    //                 { computeRootAndSiblingsIsCorrect(
    //                     p[.. |p| - 1], b[..|b| - 1],  diff(seed, 0),v1[..|p| - 1]); }
    //                 computeRootPathDiffUp(p[.. |p| - 1], b[..|b| - 1], diff(seed, 0));
    //                 computeRootPathDiffUp(p, b, seed);
    //             }
    //         } else {
    //             calc == {
    //                 computeRootPathDiffAndLeftSiblingsUp(p, b, seed, v1).0 ;
    //                 computeRootPathDiffAndLeftSiblingsUp(
    //                     p[.. |p| - 1], b[..|b| - 1], diff(b[|b| - 1], seed), v1[..|p| - 1]).0;
    //                 { computeRootAndSiblingsIsCorrect(p[.. |p| - 1], b[..|b| - 1],  diff(seed, 0),v1[..|p| - 1]); }
    //                 computeRootPathDiffUp(p, b, seed);
    //             }
    //         }
    //     }
    // }

    /**
     *  Proof that version 2 is correct.
     */
    lemma {:induction p, b, seed} computeRootAndSiblingsv2IsCorrect(p : seq<bit>, b : seq<int>, seed: int) 
        requires |p| == |b| 
        requires |p| >= 1
        /** We prove the following property: */
        ensures computeRootPathDiffAndLeftSiblingsUpv2(p, b, seed).0 == computeRootPathDiffUp(p, b, seed) 
        /** And with the post condition of computeRootPathDiffAndLeftSiblingsUpv2
         *  it gives the following general result: if the returned value is (r, xs)
         *  1. then r is the same as computeRootPathDiffUp
         *  2. xs is the the same as the computeLeftSiblingOnNextPath(p)
         */
        ensures  computeRootPathDiffAndLeftSiblingsUpv2(p, b, seed) == 
            (computeRootPathDiffUp(p, b, seed),
            computeLeftSiblingOnNextPath(p, computeAllPathDiffUp(p, b, seed), b)
            )
        decreases p
    {
        //  pre-compute the values on each node of the path.
        var nodeAt := computeAllPathDiffUp(p, b, seed);

        //  use computeRootPathDiffAndLeftSiblingsUp is correct 
        computeRootAndSiblingsIsCorrect(p, b, seed, nodeAt);

        //  Use v1equalsv2
        //  possible because nodeAt satisfies pre-condition
        computeAllDiffUpPrefixes(p, b, seed);
        v1Equalsv2(p, b, seed, nodeAt);
    }

    /** 
     *  Add requirements on |p| and values of b and v1 in computeRootPathDiffAndLeftSiblingsUp
     */
    // lemma computeRootPathDiffAndLeftSiblingsUpInATree(p: seq<bit>, r :  Tree<int>, v1 : seq<int>, v2 : seq<int>, seed : int, k : nat)

    //     requires isCompleteTree(r)       
    //     /** `r` is decorated with attribute `f`. */
    //     requires isDecoratedWith(diff, r)

    //     requires k < |leavesIn(r)|
    //     requires forall i :: k < i < |leavesIn(r)| ==> leavesIn(r)[i].v == 0

    //     /** Path to k-th leaf. */
    //     requires hasLeavesIndexedFrom(r, 0)
    //     requires 1 <= |p| == height(r) - 1      
    //     requires nodeAt(p, r) == leavesIn(r)[k]
    //     requires seed == nodeAt(p,r).v 

    //     /** Path is not to the last leaf. */
    //     requires exists i :: 0 <= i < |p| && p[i] == 0
    //     requires |v1| == |v2| == |p|
    //     requires forall i :: 0 <= i < |p| ==>
    //         v1[i] == nodeAt(p[.. i + 1],r).v 
    //     requires forall i :: 0 <= i < |p| ==>
    //         (p[i] == 1 && v2[i] == siblingAt(p[.. i + 1],r).v)
    //         || 
    //         (p[i] == 0 && v2[i] == 0)

    //     ensures computeRootPathDiffAndLeftSiblingsUp(p, v2, seed, v1).0 == r.v
    //     ensures computeRootPathDiffAndLeftSiblingsUp(p, v2, seed, v1).1 == 
    //                                          computeLeftSiblingOnNextPath(p, v1, v2)
    // {
    //     calc == {
    //         computeRootPathDiffAndLeftSiblingsUp(p, v2, seed, v1).0 ;
    //         { computeRootAndSiblingsIsCorrect(p, v2, seed, v1); }
    //          computeRootPathDiffUp(p, v2, seed) ;
    //         { computeUpEqualsComputeDown(p, v2, seed); }
    //         computeRootPathDiff(p, v2, seed) ; 
    //         computeRootPathDiff(p, v2, leavesIn(r)[k].v);
    //         { computeOnPathYieldsRootValueDiff(p, r, v2, k) ; }
    //         r.v;  
    //     }
    // }


    lemma computeRootPathDiffAndLeftSiblingsUpv2InATree(p: seq<bit>, r :  Tree<int>, v2 : seq<int>, seed : int, k : nat)

        requires isCompleteTree(r)       
        /** `r` is decorated with attribute `f`. */
        requires isDecoratedWith(diff, r)

        requires k < |leavesIn(r)|
        requires forall i :: k < i < |leavesIn(r)| ==> leavesIn(r)[i].v == 0

        /** Path to k-th leaf. */
        requires hasLeavesIndexedFrom(r, 0)
        requires 1 <= |p| == height(r) - 1      
        requires nodeAt(p, r) == leavesIn(r)[k]
        requires seed == nodeAt(p,r).v 

        /** Path is not to the last leaf. */
        requires exists i :: 0 <= i < |p| && p[i] == 0
        // requires |v1| == |v2| == |p|
        requires |v2| == |p|
        // requires forall i :: 0 <= i < |p| ==>
        //     v1[i] == nodeAt(p[.. i + 1],r).v 
        requires forall i :: 0 <= i < |p| ==>
            (p[i] == 1 && v2[i] == siblingAt(p[.. i + 1],r).v)
            || 
            (p[i] == 0 && v2[i] == 0)

        ensures computeRootPathDiffAndLeftSiblingsUpv2(p, v2, seed).0 == r.v
        ensures computeRootPathDiffAndLeftSiblingsUpv2(p, v2, seed).1 == 
                                             computeLeftSiblingOnNextPath(p, computeAllPathDiffUp(p, v2, seed), v2)
    {
        var v1 := computeAllPathDiffUp(p, v2, seed);
        //  establish pre-condition that computeAllPathDiffUp(p, v2, seed)
        //  is the same as the values of the nodes in the tree.
        assume(
           forall i :: 0 <= i < |p| ==>
            v1[i] == nodeAt(p[.. i + 1],r).v 
        );
       
        //  Proof that .0 is r.v
        calc {
            computeRootPathDiffAndLeftSiblingsUpv2(p, v2, seed).0;
            { v1Equalsv2subLemma(p, v2, seed, v1); }
            computeRootPathDiffAndLeftSiblingsUp(p, v2, seed, v1).0;
            { computeRootPathDiffAndLeftSiblingsUpInATree(p, r, v1, v2, seed, k); }
            r.v;
        }
    
        //  Proof of .1 is computeLeftSiblingOnNextPath(p, v1, v2)
        computeAllDiffUpPrefixes(p, v2, seed);
        calc {
            computeRootPathDiffAndLeftSiblingsUpv2(p, v2, seed).1;
            { v1Equalsv2(p, v2, seed, v1); }
            computeRootPathDiffAndLeftSiblingsUp(p, v2, seed, v1).1;
            { computeRootPathDiffAndLeftSiblingsUpInATree(p, r, v1, v2, seed, k); }
            computeLeftSiblingOnNextPath(p, v1, v2);
        }
        
        
    }

// computeRootPathDiffAndLeftSiblingsUpInATree(p: seq<bit>, r :  Tree<int>, v1 : seq<int>, v2 : seq<int>, seed : int, k : nat)

    /**
     *  Computing up or down yield the same result!
     */
    // lemma {:induction p, b, seed} computeUpEqualsComputeDown(p : seq<bit>, b : seq<int>, seed: int) 
    //     requires |p| == |b|
    //     ensures computeRootPathDiffUp(p, b, seed) == computeRootPathDiff(p, b, seed)
    // {
    //     if |p| <= 1 {
    //         //  Thanks Dafny
    //     } else {    
    //         //  |p| >= 2
    //         //  Split on values of p[|p| - 1]
    //         if p[|p| - 1] == 0 {
    //             calc == {
    //                 computeRootPathDiffUp(p, b, seed);
    //                 computeRootPathDiffUp(p[.. |p| - 1], b[..|b| - 1],diff(seed, 0));
    //                 //  Induction assumption
    //                 computeRootPathDiff(p[.. |p| - 1], b[..|b| - 1],diff(seed, 0));
    //                 { foo506(p, b, seed); }
    //                 computeRootPathDiff(p, b, seed);
    //             }
    //         } else  {
    //             assert(p[|p| - 1] == 1 );
    //             calc == {
    //                 computeRootPathDiffUp(p, b, seed);
    //                  computeRootPathDiffUp(p[.. |p| - 1], b[..|b| - 1],diff(b[|b| - 1], seed));
    //                 //  Induction assumption
    //                 computeRootPathDiff(p[.. |p| - 1], b[..|b| - 1], diff(b[|b| - 1], seed));
    //                 { foo506(p, b, seed); }
    //                 computeRootPathDiff(p, b, seed);
    //             }
    //         }
    //     }
    // }

   
    /**
     *  Show that if right sibling values are zero,  computeRootPathDiff
     *  computes the same result as computeRootPath.
     */
    // lemma {:induction p} computeRootPathDiffEqualscomputeRootPath(p : seq<bit>, b : seq<int>, seed: int) 
    //     requires |b| == |p| 
    //     requires forall i :: 0 <= i < |b| ==> p[i] == 0 ==> b[i] == 0
    //     ensures computeRootPathDiff(p, b, seed) == computeRootPath(p, b, diff, seed)
    //     decreases p
    // {
    //     if |p| == 0 {
    //         //  Thanks Dafny
    //     } else {
    //         //  Compute result on suffixes p[1..], b[1..]
    //         var r := computeRootPathDiff(p[1..], b[1..], seed);
    //         var r' := computeRootPath(p[1..], b[1..], diff, seed);

    //         //  Use inductive assumption on p[1..], b[1..]
    //         computeRootPathDiffEqualscomputeRootPath(p[1..], b[1..], seed);
    //         // HI implies r == r'
            
    //         calc == {   //  These terms are equal
    //             computeRootPathDiff(p, b, seed) ;
    //             if p[0] == 0 then diff(r, 0) else  diff(b[0], r);
    //             if p[0] == 0 then diff(r', 0) else  diff(b[0], r');
    //             computeRootPath(p, b, diff, seed);
    //         }
    //     }
    // }

    /**
     *  When two vectors b and b' have the same values for i such that p[i] == 1,
     *  i.e. for every left sibling b and b' coincide, then 
     *  computeRootPathDiff(p, b, seed) == computeRootPathDiff(p, b', seed)
     */
    // lemma {:induction p} sameComputeDiffPath(p : seq<bit>, b : seq<int>, b': seq<int>, seed: int)
    //     requires |b| == |p| == |b'|
    //     requires forall i :: 0 <= i < |b| ==> p[i] == 1 ==> b[i] == b'[i]
    //     ensures computeRootPathDiff(p, b, seed) == computeRootPathDiff(p, b', seed)
    //     decreases p 
    // {
    //     if |p| == 0 {
    //         //
    //     } else {
    //         var r := computeRootPathDiff(p[1..], b[1..], seed);
    //         var r' := computeRootPathDiff(p[1..], b'[1..], seed);
    //         if p[0] == 0 {
    //             calc == {
    //                 computeRootPathDiff(p, b, seed) ;
    //                 diff(r, 0) ;
    //                 // Induction on p[1..], b[1..], b'[1..], seed
    //                 { sameComputeDiffPath(p[1..], b[1..], b'[1..], seed); }  
    //                 diff(r', 0);
    //                 computeRootPathDiff(p, b', seed);
    //             }
    //         } else {
    //             calc == {
    //                 computeRootPathDiff(p, b, seed) ;
    //                 diff(b[0], r) ;
    //                 // Induction on p[1..], b[1..], b'[1..], seed
    //                 { sameComputeDiffPath(p[1..], b[1..], b'[1..], seed); }  
    //                 diff(b'[0], r');
    //                 computeRootPathDiff(p, b', seed);
    //             }
    //         }
    //     }
    // }

    // function makeB(p: seq<bit>, b: seq<int>) : seq<int> 
    //     requires |p| == |b|
    //     decreases p
    //     ensures |makeB(p, b)| == |b| && forall i :: 0 <= i < |b| ==> if p[i] == 1 then makeB(p,b)[i] == b[i] else makeB(p, b)[i] == 0 
    // {
    //     if |p| == 0 then
    //         []
    //     else    
    //         [if p[0] == 0 then 0 else b[0]] + makeB(p[1..], b[1..])
    // }

    /**
     *  Weakening of computeOnPathYieldsRootValue, requesting values on left siblings only, when
     *  merkle tree and path is not last non-null leaf.
     */
    //  lemma {:induction p, r, b} computeOnPathYieldsRootValueDiff(p : seq<bit>, r : Tree<int>, b : seq<int>, k : nat) 

    //      requires isCompleteTree(r)
    //     /** `r` is decorated with attribute `f`. */
    //     requires isDecoratedWith(diff, r)
    //     requires height(r) >= 2

    //     /**  all leaves after the k leaf are zero. */
    //     requires k < |leavesIn(r)|
    //     requires forall i :: k < i < |leavesIn(r)| ==> leavesIn(r)[i].v == 0

    //     /** p is the path to k leaf in r. */
    //     requires hasLeavesIndexedFrom(r, 0)
    //     requires |p| == height(r) - 1
    //     requires nodeAt(p, r) == leavesIn(r)[k]

    //     requires |b| == |p|
    //     /** `b` contains values at left siblings on path `p`. */
    //     requires forall i :: 0 <= i < |b| ==> p[i] == 1 ==> b[i] == siblingAt(p[..i + 1], r).v

    //     ensures r.v == computeRootPathDiff(p, b, leavesIn(r)[k].v)

    //     decreases r
    // {

    //     //  define a new seq b' that holds default values for right siblings
    //     //  and prove that pre-conditions of computeOnPathYieldsRootValue hold.

    //     // var b' : seq<int> :| |b'| == |b| && forall i :: 0 <= i < |b| ==> if p[i] == 1 then b'[i] == b[i] else b'[i] == 0 ; 
    //     var b' := makeB(p, b);

    //     leavesRightOfNodeAtPathZeroImpliesRightSiblingsOnPathZero(r, k, p, 0);
    //     assert(forall i :: 0 <= i < |p| ==> 
    //         p[i] == 0 ==> siblingAt(p[..i + 1], r).v == 0);

    //     siblingsLeft(p, r, b, b', k);
    //     assert(forall i :: 0 <= i < |p| ==> b'[i] == siblingAt(p[..i + 1], r).v);

    //     assert(forall i :: 0 <= i < |p| ==> p[i] == 0 ==> b'[i] == 0);

    //     computeOnPathYieldsRootValue(p, r, b', diff, leavesIn(r)[k].v);
    //     assert(computeRootPath(p, b', diff, leavesIn(r)[k].v) ==  r.v);
    //     computeRootPathDiffEqualscomputeRootPath(p, b', leavesIn(r)[k].v);
    //     assert(computeRootPathDiff(p, b',  leavesIn(r)[k].v) == computeRootPath(p, b', diff,  leavesIn(r)[k].v));

    //     sameComputeDiffPath(p, b, b', leavesIn(r)[k].v);
    // }

    /**
     *  Main function to compute the root value.
     */
    //  function computeRootDiffUp(p : seq<bit>, r : Tree<int>, b : seq<int>, k : nat) : int
    //     requires isCompleteTree(r)
    //     /** `r` is decorated with attribute `f`. */
    //     requires isDecoratedWith(diff, r)
    //     requires height(r) >= 2

    //     /**  all leaves after the k leaf are zero. */
    //     requires k < |leavesIn(r)|
    //     requires forall i :: k < i < |leavesIn(r)| ==> leavesIn(r)[i].v == 0

    //     /** p is the path to k leaf in r. */
    //     requires hasLeavesIndexedFrom(r, 0)
    //     requires |p| == height(r) - 1
    //     requires nodeAt(p, r) == leavesIn(r)[k]

    //     requires |b| == |p|
    //     /** `b` contains values at left siblings on path `p`. */
    //     requires forall i :: 0 <= i < |b| ==> p[i] == 1 ==> b[i] == siblingAt(p[..i + 1], r).v

    //     ensures r.v == computeRootDiffUp(p, r, b, k)
    // {
    //     //  Values on left sibling are enough to compuute r.v using computeRootPathDiff
    //     computeOnPathYieldsRootValueDiff(p, r, b, k);
    //     //  Compute computeRootUp yields same value as computeRootPathDiff
    //     computeUpEqualsComputeDown(p, b, leavesIn(r)[k].v);
    //     computeRootPathDiffUp(p, b, leavesIn(r)[k].v)
    // }


    // function incMerkle(p: seq<bit>, l : seq<int>, r : Tree<int>, b : seq<int>, k : nat) : (int, seq<int>) 

    //     requires height(r) >= 2
    //     requires  isCompleteTree(r)
    //     requires hasLeavesIndexedFrom(r, 0)

    //     requires |l| == |leavesIn(r)|
    //     requires k < |leavesIn(r)| - 1
    //     requires forall i :: k < i < |l| ==> l[i] == 0

    //     requires k < power2(height(r) - 1) 
    //     requires |b| == |p|
    //     requires isMerkle2(r, l, diff)

    //     requires p == natToBitList(k, height(r) - 1)
    //     requires forall i :: 0 <= i < |b| ==> p[i] == 1 ==> b[i] == siblingAt(p[..i + 1], r).v

    //     ensures r.v == incMerkle(p, l, r, b, k).0
    // {
    //     // var p := natToBitList(k, height(r) - 1);
    //     assert(|p| == height(r) - 1);
    //     indexOfLeafisIntValueOfPath(p, r,k);
    //     // foo200(natToBitList(k, height(r) - 1), r, k);
    //     // bitToNatToBitsIsIdentity();
    //      bitToNatToBitsIsIdentity(k, height(r) - 1);
    //     // assert(bitListToNat);
    //     // assert(nodeAt(p, r) == leavesIn(r)[k]);
    //      indexOfLeafisIntValueOfPath(p, r, k);
    //     assert(bitListToNat(p) == k ==> nodeAt(p, r) == leavesIn(r)[k]);
    //     assert(nodeAt(p, r) == leavesIn(r)[k]);

    //     (computeRootDiffUp(p, r, b, k), [])
    // }

    /** 
     *  The values on P can be computed on-the-fly.
     */
    lemma v1Equalsv2(p : seq<bit>, valOnLeftAt : seq<int>, seed: int, valOnPAt: seq<int>)
        requires |p| == |valOnLeftAt| ==  |valOnPAt|
        requires |p| >= 1
        requires forall i :: 0 <= i < |valOnPAt| ==> valOnPAt[i] == computeRootPathDiffUp(p[i + 1..], valOnLeftAt[i + 1..], seed) 

        ensures computeRootPathDiffAndLeftSiblingsUpv2(p, valOnLeftAt, seed).1 ==
            computeRootPathDiffAndLeftSiblingsUp(p, valOnLeftAt, seed, valOnPAt).1
    {
        if |p| == 1 {
            //  Thanks Dafny.
        } else {
            if p[|p| - 1] == 0 {
                var a := computeRootPathDiffAndLeftSiblingsUpv2(p, valOnLeftAt, seed);
                var b := computeRootPathDiffAndLeftSiblingsUp(p, valOnLeftAt, seed, valOnPAt);

                calc == {
                    a.1;
                    valOnLeftAt[.. |valOnLeftAt| - 1] + [seed];
                    calc == {
                        valOnPAt[|p| - 1];
                        computeRootPathDiffUp(p[|p| + 1 - 1..], valOnLeftAt[|p| + 1 - 1..], seed);
                        computeRootPathDiffUp([], [], seed);
                        seed;
                    }
                    b.1;
                }
            } else {
                //  
                var a := computeRootPathDiffAndLeftSiblingsUpv2(p, valOnLeftAt, seed);
                var b := computeRootPathDiffAndLeftSiblingsUp(p, valOnLeftAt, seed, valOnPAt);

                //  Def of computeRootPathDiffAndLeftSiblingsUpv2 for p[|p| - 1] == 1
                var a1 := computeRootPathDiffAndLeftSiblingsUpv2(
                    p[.. |p| - 1], 
                    valOnLeftAt[..|valOnLeftAt| - 1],  
                    diff(valOnLeftAt[|valOnLeftAt| - 1], seed));
                //  def of computeRootPathDiffAndLeftSiblingsUp for p[|p| - 1] == 1
                var b1 := computeRootPathDiffAndLeftSiblingsUp(
                    p[.. |p| - 1], valOnLeftAt[..|valOnLeftAt| - 1], diff(valOnLeftAt[|valOnLeftAt| - 1], seed), valOnPAt[..|p| - 1]);
                calc == {
                    computeRootPathDiffAndLeftSiblingsUpv2(p, valOnLeftAt, seed).1;
                    a1.1 + [seed];
                }
                calc == {
                    computeRootPathDiffAndLeftSiblingsUp(p, valOnLeftAt, seed, valOnPAt).1;
                    b1.1 + [valOnPAt[|p| - 1]];
                }
                calc == {
                    valOnPAt[|p| - 1];
                    computeRootPathDiffUp(p[|p| + 1 - 1..], valOnLeftAt[|p| + 1 - 1..], seed);
                    computeRootPathDiffUp([], [], seed);
                    seed;
                }
                //  Establish pre-condition for use of inductive hypothesis on p[.. |p| - 1]
                prefixOfComputation(p, valOnLeftAt, seed, valOnPAt);
                calc == {
                    a1.1;
                    { v1Equalsv2(p[.. |p| - 1], valOnLeftAt[..|valOnLeftAt| - 1], diff(valOnLeftAt[|valOnLeftAt| - 1], seed), valOnPAt[..|p| - 1]); } 
                    b1.1;
                }
            }
        }
    }

     lemma v1Equalsv2subLemma(p : seq<bit>, valOnLeftAt : seq<int>, seed: int, valOnPAt: seq<int>)
        requires |p| == |valOnLeftAt| ==  |valOnPAt|
        requires |p| >= 1
        ensures computeRootPathDiffAndLeftSiblingsUp(p, valOnLeftAt, seed, valOnPAt).0 ==
            computeRootPathDiffAndLeftSiblingsUpv2(p, valOnLeftAt, seed).0
    {   //  Thanks Dafny.
    }

    /**
     *  A useful lemma need in the proof of v1Equalsv2 when |p| > 1 and p[|p| - 1] == 1.
     *  
     *  It states that the values on  valOnPAt[..|p| - 1] (valOnPAt minus last element) must
     *  coincide with computations of prefixes of p[.. |p| - 1] starting from a seed that 
     *  is the result of the computation of diff using the last values (node and it sibling).
     *
     *  @note   A tedious proof with lots of indices but not hard.
     */
    // lemma prefixOfComputation(p : seq<bit>, valOnLeftAt : seq<int>, seed: int, valOnPAt: seq<int>) 
    //     requires |p| == |valOnLeftAt| ==  |valOnPAt|
    //     requires |p| >= 2
    //     requires forall i :: 0 <= i < |valOnPAt| ==> valOnPAt[i] == computeRootPathDiffUp(p[i + 1..], valOnLeftAt[i + 1..], seed) 
    //     ensures p[|p| - 1] == 1 ==> forall i :: 0 <= i < |valOnLeftAt[..|valOnLeftAt| - 1]| ==> 
    //                 valOnPAt[..|p| - 1][i] == computeRootPathDiffUp(p[.. |p| - 1][i + 1..], valOnLeftAt[..|valOnLeftAt| - 1][i + 1..], diff(valOnLeftAt[|valOnLeftAt| - 1], seed)) 
    // {
    //     if p[|p| - 1] == 1 {
    //         forall (i : nat  | 0 <= i < |valOnPAt[.. |valOnPAt| - 1]|)
    //                 ensures valOnPAt[.. |valOnPAt| - 1][i] == computeRootPathDiffUp( p[.. |p| - 1][i + 1..], valOnLeftAt[.. |valOnLeftAt| - 1][i + 1..], diff(valOnLeftAt[|valOnLeftAt| - 1], seed)) 
    //         {
    //             calc == {
    //                 computeRootPathDiffUp(
    //                             p[..|p| - 1][i + 1..], 
    //                             valOnLeftAt[..|valOnLeftAt| - 1][i + 1 ..],
    //                             diff(valOnLeftAt[|valOnLeftAt| - 1], seed)) ;
    //                 calc == {
    //                         valOnLeftAt[i + 1..][..|valOnLeftAt[i + 1..]| - 1];
    //                         valOnLeftAt[..|valOnLeftAt| - 1][i + 1 ..];
    //                 }
    //                 computeRootPathDiffUp(
    //                             p[..|p| - 1][i + 1..], 
    //                             valOnLeftAt[i + 1..][..| valOnLeftAt[i + 1..]| - 1],
    //                             diff(valOnLeftAt[|valOnLeftAt| - 1], seed)) ;
    //                 calc == {
    //                         p[i + 1..][.. |p[i + 1..]| - 1];
    //                         p[..|p| - 1][i + 1..];
    //                 }
    //                 computeRootPathDiffUp(
    //                             p[i + 1..][.. |p[i + 1..]| - 1], 
    //                             valOnLeftAt[i + 1..][..| valOnLeftAt[i + 1..]| - 1],
    //                             diff(valOnLeftAt[|valOnLeftAt| - 1], seed)) ;
    //                 calc == {
    //                         p[i + 1..][|p[i + 1..]| - 1];
    //                         1;
    //                 }
    //                 computeRootPathDiffUp(p[i + 1..], valOnLeftAt[i + 1..],  diff(valOnLeftAt[|valOnLeftAt| - 1], diff(valOnLeftAt[|valOnLeftAt| - 1], seed))); 
    //                 //  use requires
    //                 valOnPAt[i];
    //                 //  as i < |p| - 2, valOnPAt[i] is same as valOnPAt[..|p| - 1][i]
    //                 valOnPAt[..|p| - 1][i];
    //             }
    //         }
    //     }
    // }
 }