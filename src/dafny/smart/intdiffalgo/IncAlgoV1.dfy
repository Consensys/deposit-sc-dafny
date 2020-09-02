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
include "../helpers/SeqHelpers.dfy"
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
    import opened SeqHelpers
    import opened Trees

    /**
     *  Compute diff root and collect siblings of next path.
     *  
     *  @param  p           The path.
     *  @param  valOnLeftAt The values of the left siblings of nodes on path `p`.
     *  @param  seed        The value at nodeAt(p).
     *  @param  valOnPAt    The values of the nodes on the path p.
     *  @returns            The value of diff at the root and a vector of values of
     *                      for the left siblings on nextPath(p).
     */
    function computeRootPathDiffAndLeftSiblingsUp(
        p : seq<bit>, valOnLeftAt : seq<int>, seed: int, valOnPAt: seq<int>) : (int, seq<int>)
        requires |p| == |valOnLeftAt| == |valOnPAt|
        requires |p| >= 1
        /*  This post-condition follows easily from the defs of the functions.
         *  The fact that computeRootPathDiffAndLeftSiblingsUp.0 is the same as
         *  computeRootPathDiff requires some hints (ncluding this post-condition) 
         *  and is proved in computeRootAnSiblingsIsCorrect.
         */
        ensures 
            computeRootPathDiffAndLeftSiblingsUp(p, valOnLeftAt, seed, valOnPAt).1 
            == 
            computeLeftSiblingOnNextPath(p, valOnPAt, valOnLeftAt)
        
        decreases p
    {
     if |p| == 1 then
        var r := computeRootPathDiff(p, valOnLeftAt, seed);
        //  if p[0] == 0, the left sibling of nextpath is at p[0] and the value is valOnP
        //  Otherwise, if p[0] == 1, the sibling for nextPath at this level is a right sibling and
        //  we do not care about the value of the second component.
        (r, if first(p) == 0 then valOnPAt else valOnLeftAt) 
    else 
        if last(p) == 0 then
            var r := computeRootPathDiffAndLeftSiblingsUp(
                    init(p), init(valOnLeftAt),  diff(seed, 0), init(valOnPAt));
                    (r.0, init(valOnLeftAt) + [last(valOnPAt)])
        else      
            var r :=  computeRootPathDiffAndLeftSiblingsUp(
                    init(p), init(valOnLeftAt), diff(last(valOnLeftAt), seed), init(valOnPAt));
                     /* The last value [valOnLeftAt[|valOnLeftAt| - 1]] is not used on 
                        the next path as it is not a leftSibling of a node of next path.
                        at this level. As a consequence we can use any value to append to
                        the second component of the result .1. We just use the old value 
                        [valOnLeftAt[|valOnLeftAt| - 1] as it will enable us to "modify" 
                        in-place a unique array in the imperative version. */
                    (r.0, r.1 + [last(valOnLeftAt)])
    }

    /**
     *  This version switches to computeRootPathDiffUp only as soon as 
     *  we encounter a path p such that last(p) == 0.
     */
    function computeRootPathDiffAndLeftSiblingsUpOpt(
        p : seq<bit>, valOnLeftAt : seq<int>, seed: int, valOnPAt: seq<int>) : (int, seq<int>)
        requires |p| == |valOnLeftAt| == |valOnPAt|
        requires |p| >= 1

        /** Optimised computes same result as non-optimised. */
        ensures 
            computeRootPathDiffAndLeftSiblingsUp(p, valOnLeftAt, seed, valOnPAt)
            == 
            computeRootPathDiffAndLeftSiblingsUpOpt(p, valOnLeftAt, seed, valOnPAt)

        decreases p
    {
     if |p| == 1 then
        var r := computeRootPathDiff(p, valOnLeftAt, seed);
        (r, if first(p) == 0 then valOnPAt else valOnLeftAt) 
    else 
        if last(p) == 0 then
            //  Inline the proof that optimised computes same as non optimised
            //  Compute resuklt with non-optimised
            ghost var r1 := computeRootPathDiffAndLeftSiblingsUp(
                    init(p), init(valOnLeftAt),  diff(seed, 0), init(valOnPAt));
            
            //  This is the optimisation: we compute RootPathDiff only
            var r := computeRootPathDiffUp(init(p), init(valOnLeftAt),  diff(seed, 0));
            //  Prove that r1.0 == r
            calc == {
                r1.0;
                {  computeRootAndSiblingsIsCorrect(init(p),  init(valOnLeftAt),  diff(seed, 0),
                     init(valOnPAt)) ; }
                computeRootPathDiffUp(init(p),  init(valOnLeftAt),  diff(seed, 0));
                r;
            }
            (r, init(valOnLeftAt) + [last(valOnPAt)])
        else      
            var r :=  computeRootPathDiffAndLeftSiblingsUp(
                    init(p), init(valOnLeftAt), diff(last(valOnLeftAt), seed), init(valOnPAt));
                    (r.0, r.1 + [last(valOnLeftAt)])
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
            if last(p) == 0 {
                calc == {
                    computeRootPathDiffAndLeftSiblingsUp(p, b, seed, v1).0;
                    computeRootPathDiffAndLeftSiblingsUp(
                        init(p), init(b),  diff(seed, 0), init(v1)).0;
                    { computeRootAndSiblingsIsCorrect(
                       init(p), init(b),  diff(seed, 0), init(v1)) ; }
                    computeRootPathDiffUp(init(p), init(b), diff(seed, 0));
                    computeRootPathDiffUp(p, b, seed);
                }
            } else {
                calc == {
                    computeRootPathDiffAndLeftSiblingsUp(p, b, seed, v1).0 ;
                    computeRootPathDiffAndLeftSiblingsUp(
                        init(p), init(b), diff(last(b), seed), init(v1)).0;
                    { computeRootAndSiblingsIsCorrect(init(p), init(b),  diff(seed, 0), init(v1)); }
                    computeRootPathDiffUp(p, b, seed);
                }
            }
        }
    }

    /** 
     *  Add requirements on |p| and values of b and v1 in computeRootPathDiffAndLeftSiblingsUp
     */
    lemma {:induction p} computeRootPathDiffAndLeftSiblingsUpInATree(p: seq<bit>, r :  Tree<int>, v1 : seq<int>, v2 : seq<int>, seed : int, k : nat)

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
            v1[i] == nodeAt(take(p, i + 1),r).v 
        requires forall i :: 0 <= i < |p| ==>
            (p[i] == 1 && v2[i] == siblingAt(take(p, i + 1),r).v)
            || 
            (p[i] == 0 && v2[i] == 0)

        /** Non-optimsied version is correct. */
        ensures computeRootPathDiffAndLeftSiblingsUp(p, v2, seed, v1).0 == r.v
        ensures computeRootPathDiffAndLeftSiblingsUp(p, v2, seed, v1).1 
                                                    == computeLeftSiblingOnNextPath(p, v1, v2)

        /** Optimsied is correct as they compute the same result. */
        ensures computeRootPathDiffAndLeftSiblingsUpOpt(p, v2, seed, v1).0 == r.v
        ensures computeRootPathDiffAndLeftSiblingsUpOpt(p, v2, seed, v1).1 
                                                    == computeLeftSiblingOnNextPath(p, v1, v2)
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

 }