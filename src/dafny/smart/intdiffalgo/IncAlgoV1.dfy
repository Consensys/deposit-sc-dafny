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
 
include "DiffTree.dfy"
include "../trees/CompleteTrees.dfy"
include "../synthattribute/ComputeRootPath.dfy"
include "../synthattribute/GenericComputation.dfy"
include "../helpers/Helpers.dfy"
include "../synthattribute/LeftSiblings.dfy"
include "../MerkleTrees.dfy"
include "../paths/NextPathInCompleteTreesLemmas.dfy"
include "../paths/PathInCompleteTrees.dfy"
include "../seqofbits/SeqOfBits.dfy"
include "../trees/Trees.dfy"

module IncAlgoV1 {
 
    import opened DiffTree
    import opened CompleteTrees
    import opened ComputeRootPath
    import opened GenericComputation
    import opened Helpers
    import opened LeftSiblings
    import opened MerkleTrees
    import opened NextPathInCompleteTreesLemmas
    import opened PathInCompleteTrees
    import opened SeqOfBits
    import opened Trees

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
    function computeRootPathDiffAndLeftSiblingsUp(
        p : seq<bit>, valOnLeftAt : seq<int>, seed: int, valOnPAt: seq<int>) : (int, seq<int>)
        requires |p| == |valOnLeftAt| == |valOnPAt|
        requires |p| >= 1
        /** This post-condition follows easily from the defs of the functions.
         *  The fact that computeRootPathDiffAndLeftSiblingsUp.0 is the same as
         *  computeRootPathDiff requires some hints and is proved in computeRootAnSiblingsIsCorrect.
         */
        ensures computeRootPathDiffAndLeftSiblingsUp(p, valOnLeftAt, seed, valOnPAt).1 == computeLeftSiblingOnNextPath(p, valOnPAt, valOnLeftAt)
        
        decreases p
    {
     if |p| == 1 then
        var r := computeRootPathDiff(p, valOnLeftAt, seed);
        //  if p[0] == 0, the left sibling of nextpath is at p[0] and the value is valOnP
        //  Otherwise, if p[0] == 1, the sibling for nextPath at this level is a right sibling and
        //  we do not care about the value of the second component.
        (r, if p[0] == 0 then valOnPAt else valOnLeftAt) 
    else 
        if p[|p| - 1] == 0 then
            var r := computeRootPathDiffAndLeftSiblingsUp(
                    p[.. |p| - 1], valOnLeftAt[..|valOnLeftAt| - 1],  diff(seed, 0), valOnPAt[..|p| - 1]);
                    (r.0, valOnLeftAt[.. |valOnLeftAt| - 1] + [valOnPAt[|p| - 1]])
        else      
            var r :=  computeRootPathDiffAndLeftSiblingsUp(
                    p[.. |p| - 1], valOnLeftAt[..|valOnLeftAt| - 1], diff(valOnLeftAt[|valOnLeftAt| - 1], seed), valOnPAt[..|p| - 1]);
                     /* The last value [valOnLeftAt[|valOnLeftAt| - 1]] is not used on 
                        the next path as it is not a leftSibling of a node of next path.
                        at this level. As a consequence we can use any value to append to
                        the second component of the result .1. We just use the old value 
                        [valOnLeftAt[|valOnLeftAt| - 1] as it will enable us to "modify" 
                        in-place a unique array in the imperative version. */
                    (r.0, r.1 + [valOnLeftAt[|valOnLeftAt| - 1]])
    }

    /**
     *  For path of size >= 2, computeRootPathDiffAndLeftSiblingsUp and computeRootPathDiffUp
     *  yield the same result.
     */
    lemma {:induction p, b, seed, v1} computeRootAndSiblingsIsCorrect(p : seq<bit>, b : seq<int>, seed: int, v1: seq<int>) 
        requires |p| == |b| == |v1|
        requires |p| >= 1
        /** We prove the following property: */
        ensures computeRootPathDiffAndLeftSiblingsUp(p, b, seed, v1).0 == computeRootPathDiffUp(p, b, seed) 
        /** And with the post condition of computeRootPathDiffAndLeftSiblingsUp 
         *  it gives the following general result: if the returned value is (r, xs)
         *  1. then r is the same as computeRootPathDiffUp
         *  2. xs is the the same as the computeLeftSiblingOnNextPath(p)
         */
        ensures  computeRootPathDiffAndLeftSiblingsUp(p, b, seed, v1) == 
            (computeRootPathDiffUp(p, b, seed),
            computeLeftSiblingOnNextPath(p, v1, b)
            )
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
                    { computeRootAndSiblingsIsCorrect(
                        p[.. |p| - 1], b[..|b| - 1],  diff(seed, 0),v1[..|p| - 1]); }
                    computeRootPathDiffUp(p[.. |p| - 1], b[..|b| - 1], diff(seed, 0));
                    computeRootPathDiffUp(p, b, seed);
                }
            } else {
                calc == {
                    computeRootPathDiffAndLeftSiblingsUp(p, b, seed, v1).0 ;
                    computeRootPathDiffAndLeftSiblingsUp(
                        p[.. |p| - 1], b[..|b| - 1], diff(b[|b| - 1], seed), v1[..|p| - 1]).0;
                    { computeRootAndSiblingsIsCorrect(p[.. |p| - 1], b[..|b| - 1],  diff(seed, 0),v1[..|p| - 1]); }
                    computeRootPathDiffUp(p, b, seed);
                }
            }
        }
    }

    /** 
     *  Add requirements on |p| and values of b and v1 in computeRootPathDiffAndLeftSiblingsUp
     */
    lemma computeRootPathDiffAndLeftSiblingsUpInATree(p: seq<bit>, r :  Tree<int>, v1 : seq<int>, v2 : seq<int>, seed : int, k : nat)

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
        requires |v1| == |v2| == |p|
        requires forall i :: 0 <= i < |p| ==>
            v1[i] == nodeAt(p[.. i + 1],r).v 
        requires forall i :: 0 <= i < |p| ==>
            (p[i] == 1 && v2[i] == siblingAt(p[.. i + 1],r).v)
            || 
            (p[i] == 0 && v2[i] == 0)

        ensures computeRootPathDiffAndLeftSiblingsUp(p, v2, seed, v1).0 == r.v
        ensures computeRootPathDiffAndLeftSiblingsUp(p, v2, seed, v1).1 == 
                                             computeLeftSiblingOnNextPath(p, v1, v2)
    {
        calc == {
            computeRootPathDiffAndLeftSiblingsUp(p, v2, seed, v1).0 ;
            { computeRootAndSiblingsIsCorrect(p, v2, seed, v1); }
             computeRootPathDiffUp(p, v2, seed) ;
            { computeUpEqualsComputeDown(p, v2, seed); }
            computeRootPathDiff(p, v2, seed) ; 
            computeRootPathDiff(p, v2, leavesIn(r)[k].v);
            { computeOnPathYieldsRootValueDiff(p, r, v2, k) ; }
            r.v;  
        }
    }

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
 }