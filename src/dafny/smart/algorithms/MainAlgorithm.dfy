/*
 * Copyright 2021 ConsenSys Software Inc.
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
 
include "../trees/CompleteTrees.dfy"
include "../synthattribute/ComputeRootPath.dfy"
include "../synthattribute/GenericComputation.dfy"
include "../helpers/Helpers.dfy"
include "../paths/NextPathInCompleteTreesLemmas.dfy"
include "../paths/PathInCompleteTrees.dfy"
include "../seqofbits/SeqOfBits.dfy"
include "../helpers/SeqHelpers.dfy"
include "../trees/Trees.dfy"

/**
 *  Algorithm to compute root value and left siblings on next path concurrently.
 */
module MainAlgorithm {
 
    import opened CompleteTrees
    import opened ComputeRootPath
    import opened GenericComputation
    import opened Helpers
    import opened NextPathInCompleteTreesLemmas
    import opened PathInCompleteTrees
    import opened SeqOfBits
    import opened SeqHelpers
    import opened Trees

    ///////////////////////////////////////////////////////////////////////////
    //  Main algorithm
    ///////////////////////////////////////////////////////////////////////////

    /**
     *  Compute root value and collect siblings of next path.
     *  
     *  @param  p           The path.
     *  @param  left        The values of the left siblings of nodes on path `p`.
     *  @param  right       The values of the left siblings of nodes on path `p`.
     *  @param  seed        The value at nodeAt(p).
     *  @param  f           The binary operation to compute.
     *  @returns            The value of diff at the root and a vector of values of
     *                      for the left siblings on nextPath(p).
     */
    function computeRootAndLeftSiblingsUp<T>(
        p : seq<bit>, left : seq<T>, right : seq<T>,  f : (T, T) -> T, seed: T) : (T, seq<T>)
        requires |p| == |left| == |right| 
        requires |p| >= 1
        
        ensures computeRootAndLeftSiblingsUp(p, left, right, f, seed).0 
            == computeRootLeftRightUp(p, left, right, f, seed)

        ensures  computeRootAndLeftSiblingsUp(p, left, right, f, seed).1 
            == computeLeftSiblingOnNextPathFromLeftRight(p, left, right, f, seed)

        decreases p
    {
     if |p| == 1 then
        var r := computeRootLeftRightUp(p, left, right, f,  seed);
        /*  If p[0] == 0, the left sibling of nextpath is at p[0] and the value is valOnP
         *  Otherwise, if p[0] == 1, the sibling for nextPath at this level is a right sibling and
         *  we do not care about the value of the second component, so we copy the previous one in `left`.
         */
        (r, if first(p) == 0 then [seed] else left) 
    else 
        if last(p) == 0 then
            var r := computeRootAndLeftSiblingsUp(
                    init(p), init(left),  init(right), f, f(seed, last(right)));
            (r.0, init(left) + [seed])
        else      
            var r :=  computeRootAndLeftSiblingsUp(
                    init(p), init(left), init(right), f, f(last(left), seed));
                /*  The nextPath is of the form nextPath(init(p)) + [0].
                 *  So the sibling at this level is a right sibling and the value we store in the
                 *  result for this result is irrelevant. We choose to keep the value of the previous left
                 *  sibling from v2 in order to allow optimisations in the impertive version of the algorithm.
                 */
            (r.0, r.1 + [last(left)])
    }

    ///////////////////////////////////////////////////////////////////////////
    //  Main correctness proof.
    ///////////////////////////////////////////////////////////////////////////   
    
    /** 
     *  Correctness proof in a tree.
     *  
     *  @param  p           The path.
     *  @param  r           A complete tree.
     *  @param  left        The values of the left siblings of nodes on path `p` in `r`.
     *  @param  right       The values of the right siblings of nodes on path `p` in `r`.
     *  @param  f           The binary operation to compute.
     *  @param  seed        The value at nodeAt(p) (leaf).
     *  @param  d           The default value for type `T`.
     *  @param  k           The index of a leaf (not last) in `r`.
     */
    lemma {:induction p} computeRootAndLeftSiblingsUpCorrectInATree<T>(
            p: seq<bit>, r :  Tree<T>, left: seq<T>, right: seq<T>, f : (T, T) -> T, seed : T, d : T, k : nat)

        requires isCompleteTree(r)       
        requires isDecoratedWith(f, r)
        requires hasLeavesIndexedFrom(r, 0)

        requires k < |leavesIn(r)| - 1
        requires forall i :: k < i < |leavesIn(r)| ==> leavesIn(r)[i].v == d
        requires leavesIn(r)[k].v == seed

        /** Path to k-th leaf. */
        requires 1 <= |p| == height(r)   
        requires bitListToNat(p) == k 

        requires |left| == |right| == |p|

         /** Left and right contains siblings left and right values.  */
        requires forall i :: 0 <= i < |p| ==>
            siblingAt(take(p, i + 1), r).v == 
                if p[i] == 0 then 
                    right[i]
                else 
                    left[i]

        /** Path is not to the last leaf. */
        ensures exists i :: 0 <= i < |p| && p[i] == 0

        /** Non-optimsied version is correct. */
        ensures computeRootAndLeftSiblingsUp(p, left, right, f, seed).0 == r.v
        ensures forall i :: 0 <= i < |p| && nextPath(p)[i] == 1 ==> 
                (computeRootAndLeftSiblingsUp(p, left, right, f, seed).1)[i] == siblingAt(take(nextPath(p), i + 1),r).v

    {
        //  exists p[i] == 0, necessary to apply computeLeftSiblingOnNextPathFromLeftRightIsCorrectInATree lemma
        calc ==> {
            true;
            { pathToLeafInInitHasZero(p, r, k); }
            exists i ::  0 <= i < |p| && p[i] == 0;
        }
        
        //   we have computeRootAndLeftSiblingsUp(p, left, right, f, seed).0 == computeRootLeftRightUp(p, left, right, f, seed)
        computeLeftRightUpEqualsComputeLeftRight(p, left, right, f, seed);

        //  Prove that seed == nodeAt(p, r).v, ncessary to apply lemma computeRootLeftRightIsCorrectForTree
        calc == {
            nodeAt(p, r);
            { leafAtPathIsIntValueOfPath(p, r, k, 0) ; }
            leavesIn(r)[k];
        }
        computeRootLeftRightIsCorrectForTree(p, r, left, right, f, seed);
        
        computeLeftSiblingOnNextPathFromLeftRightIsCorrectInATree(p, r, left, right, f, seed, k);
    }
 
 }