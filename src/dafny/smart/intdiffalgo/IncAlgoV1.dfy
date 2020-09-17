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
 
include "../trees/CompleteTrees.dfy"
include "../synthattribute/ComputeRootPath.dfy"
include "../synthattribute/GenericComputation.dfy"
include "../helpers/Helpers.dfy"
// include "../synthattribute/Siblings.dfy"
// include "../MerkleTrees.dfy"
include "../paths/NextPathInCompleteTreesLemmas.dfy"
include "../paths/PathInCompleteTrees.dfy"
include "../seqofbits/SeqOfBits.dfy"
include "../helpers/SeqHelpers.dfy"
include "../trees/Trees.dfy"

module IncAlgoV1 {
 
    import opened CompleteTrees
    import opened ComputeRootPath
    import opened GenericComputation
    import opened Helpers
    // import opened Siblings
    // import opened MerkleTrees
    import opened NextPathInCompleteTreesLemmas
    import opened PathInCompleteTrees
    import opened SeqOfBits
    import opened SeqHelpers
    import opened Trees

    /**
     *  Compute diff root and collect siblings of next path.
     *  
     *  @param  p           The path.
     *  @param  left        The values of the left siblings of nodes on path `p`.
     *  @param  right       The values of the left siblings of nodes on path `p`.
     *  @param  seed        The value at nodeAt(p).
     *  @param  valOnPAt    The values of the nodes on the path p.
     *  @param  f           The binary operation to compute.
     *  @returns            The value of diff at the root and a vector of values of
     *                      for the left siblings on nextPath(p).
     */
    function computeRootAndLeftSiblingsUp<T>(
        p : seq<bit>, left : seq<T>, right : seq<T>,  f : (T, T) -> T, seed: T, valOnPAt: seq<T>) : (T, seq<T>)
        requires |p| == |left| == |right| == |valOnPAt|
        requires |p| >= 1
        /*  This post-condition follows easily from the defs of the two functions.
         *  The fact that computeRootAndLeftSiblingsUp.0 is the same as
         *  computeRootPath requires some hints (ncluding this post-condition) 
         *  and is proved in computeRootAnSiblingsIsCorrect.
         */
        ensures 
            computeRootAndLeftSiblingsUp(p, left, right, f, seed, valOnPAt).1 
            == 
            computeLeftSiblingOnNextPath(p, valOnPAt, left)
        
        decreases p
    {
     if |p| == 1 then
        var r := computeRootLeftRightUp(p, left, right, f,  seed);
        /*  If p[0] == 0, the left sibling of nextpath is at p[0] and the value is valOnP
         *  Otherwise, if p[0] == 1, the sibling for nextPath at this level is a right sibling and
         *  we do not care about the value of the second component, so we copy the previous one in `left`.
         */
        (r, if first(p) == 0 then valOnPAt else left) 
    else 
        if last(p) == 0 then
            var r := computeRootAndLeftSiblingsUp(
                    init(p), init(left),  init(right), f, f(seed, last(right)), init(valOnPAt));
            (r.0, init(left) + [last(valOnPAt)])
        else      
            var r :=  computeRootAndLeftSiblingsUp(
                    init(p), init(left), init(right), f, f(last(left), seed), init(valOnPAt));
                /*  The nextPath is of the form nextPath(init(p)) + [0].
                 *  So the sibling at this level is a right sibling and the value we store in the
                 *  result for this result is irrelevant. We choose to keep the value of the previous left
                 *  sibling from v2 in order to allow optimisations in the impertive version of the algorithm.
                 */
            (r.0, r.1 + [last(left)])
    }

    //  Correctness proofs.

    /**
     *  For path of size >= 2, computeRootPathDiffAndLeftSiblingsUp and computeRootLeftRightUp
     *  yield the same result.
     *  
     *  @param  p           The path.
     *  @param  left        The values of the left siblings of nodes on path `p`.
     *  @param  right       The values of the left siblings of nodes on path `p`.
     *  @param  seed        The value at nodeAt(p).
     *  @param  valOnPAt    The values of the nodes on the path p.
     *  @param  f           The binary operation to compute.
     */
    lemma {:induction p, left, right} computeRootAndSiblingsIsCorrect<T>(p : seq<bit>, left : seq<T>, right: seq<T>, f : (T, T) -> T, seed: T, valOnP: seq<T>) 
        requires |p| == |left| == |right| == |valOnP|
        requires |p| >= 1
        /* We prove the following property: */
        ensures computeRootAndLeftSiblingsUp(p, left, right, f, seed, valOnP).0 == computeRootLeftRightUp(p, left, right, f, seed)
        /*  And combining with the post condition of computeRootAndLeftSiblingsUp 
         *  it gives the following general result: if the returned value is (r, xs)
         *  1. then r is the same as computeRoot
         *  2. xs is the the same as the computeLeftSiblingOnNextPath(p)
         */
        ensures  computeRootAndLeftSiblingsUp(p, left, right, f, seed, valOnP) == 
            (computeRootLeftRightUp(p, left, right, f, seed),
            computeLeftSiblingOnNextPath(p, valOnP, left)
            )
        decreases p
    {
        if |p| == 1 {
            //  Thanks Dafny
            calc == {
                computeRootAndLeftSiblingsUp(p, left, right, f, seed, valOnP).0;
                computeRootLeftRightUp(p, left, right, f, seed);
                { computeLeftRightUpEqualsComputeLeftRight(p, left, right, f, seed); }
                computeRootLeftRightUp(p, left, right, f, seed);
            }
        } else {
            //  Define result on node according to last(p)
            var x := if last(p) == 0 then f(seed, last(right)) else  f(last(left), seed);
            //  Induction on init(p)
            calc == {
                    computeRootAndLeftSiblingsUp(p, left, right, f, seed, valOnP).0;
                    computeRootAndLeftSiblingsUp(init(p), init(left),  init(right), f, x, init(valOnP)).0;
                    { computeRootAndSiblingsIsCorrect(init(p), init(left), init(right), f,  x, init(valOnP)) ; }
                    computeRootLeftRightUp(init(p), init(left), init(right), f, x);
                    computeRootLeftRightUp(p, left, right, f, seed);
                }
        }
    }

    /** 
     *  Correctness proof in a tree.
     *  
     *  @param  p           The path.
     *  @param  r           A complete tree.
     *  @param  left        The values of the left siblings of nodes on path `p` in `r`.
     *  @param  right       The values of the right siblings of nodes on path `p` in `r`.
     *  @param  valOnPAt    The values of the nodes on the path p.
     *  @param  f           The binary operation to compute.
     *  @param  seed        The value at nodeAt(p) (leaf).
     *  @param  d           The default value for type `T`.
     *  @param  k           The index of a leaf (not last) in `r`.
     */
    lemma {:induction p} computeRootPathDiffAndLeftSiblingsUpInATree<T>(
            p: seq<bit>, r :  Tree<T>, left: seq<T>, right: seq<T>, valOnP : seq<T>, f : (T, T) -> T, seed : T, d : T, k : nat)

        requires isCompleteTree(r)       
        requires isDecoratedWith(f, r)
        requires hasLeavesIndexedFrom(r, 0)

        requires k < |leavesIn(r)|
        requires forall i :: k < i < |leavesIn(r)| ==> leavesIn(r)[i].v == d
        requires leavesIn(r)[k].v == seed

        /** Path to k-th leaf. */
        requires 1 <= |p| == height(r)   
        requires bitListToNat(p) == k 
        // nodeAt(p, r) == leavesIn(r)[k]
        // requires seed == nodeAt(p,r).v 

        /** Path is not to the last leaf. */
        requires exists i :: 0 <= i < |p| && p[i] == 0
        requires |left| == |right| == |valOnP| == |p|

        requires forall i :: 0 <= i < |p| ==> valOnP[i] == nodeAt(take(p, i + 1),r).v 

        /** Left and right contain values of left and siblings of `p` in `r`. */
        requires forall i :: 0 <= i < |p| ==>
            (p[i] == 1 && left[i] == siblingAt(take(p, i + 1),r).v)
            || 
            (p[i] == 0 && right[i] == siblingAt(take(p, i + 1),r).v)

        /** Non-optimsied version is correct. */
        ensures computeRootAndLeftSiblingsUp(p, left, right, f, seed, valOnP).0 == r.v
        ensures computeRootAndLeftSiblingsUp(p, left, right, f, seed, valOnP).1 
                                                    == computeLeftSiblingOnNextPath(p, valOnP, left)

        /** Optimsied is correct as they compute the same result. */
        // ensures computeRootPathDiffAndLeftSiblingsUpOpt(p, v2, seed, v1).0 == r.v
        // ensures computeRootPathDiffAndLeftSiblingsUpOpt(p, v2, seed, v1).1 
        //                                             == computeLeftSiblingOnNextPath(p, v1, v2)
    {
        //  Prove that seed == nodeAt(p, r).v
        calc == {
            nodeAt(p, r).v;
            { leafAtPathIsIntValueOfPath(p, r, k, 0) ; }
            leavesIn(r)[k].v;
            seed;
        }
        calc == {
            computeRootAndLeftSiblingsUp(p, left, right, f, seed, valOnP).0 ;
            { computeRootAndSiblingsIsCorrect(p, left, right, f, seed, valOnP); }
            computeRootLeftRightUp(p, left, right, f, seed) ;
            { computeLeftRightUpEqualsComputeLeftRight(p, left, right, f, seed); }
            computeRootLeftRight(p, left, right, f, seed) ; 
            { computeRootLeftRightIsCorrectForTree(p, r, left, right, f, seed) ; }
            r.v;  
        }
    }

     /**
     *  This version switches to computeRootPathDiffUp only as soon as 
     *  we encounter a path p such that last(p) == 0.
     *
     *  @param  p           The path.
     *  @param  left        The values of the left siblings of nodes on path `p`.
     *  @param  right       The values of the left siblings of nodes on path `p`.
     *  @param  seed        The value at nodeAt(p).
     *  @param  valOnPAt    The values of the nodes on the path p.
     *  @param  f           The binary operation to compute.
     */
    function computeRootAndLeftSiblingsUpOpt<T>(
        p : seq<bit>, left : seq<T>, right : seq<T>, f : (T, T) -> T, seed: T, valOnP: seq<T>) : (T, seq<T>)
        requires |p| == |left| == |right| == |valOnP|
        requires |p| >= 1

        /** Optimised computes same result as non-optimised. */
        ensures 
            computeRootAndLeftSiblingsUp(p, left, right, f, seed, valOnP)
            == 
            computeRootAndLeftSiblingsUpOpt(p, left, right, f, seed, valOnP)

        decreases p
    {
     if |p| == 1 then
        var r := computeRootLeftRightUp(p, left, right, f, seed);
        (r, if first(p) == 0 then valOnP else left) 
    else 
        if last(p) == 0 then
            //  Inline the proof that optimised computes same as non optimised
            //  Compute resuklt with non-optimised
            ghost var r1 := computeRootAndLeftSiblingsUp(
                    init(p), init(left), init(right), f,  f(seed, last(right)), init(valOnP));
            
            //  This is the optimisation: we compute RootPathDiff only
            var r := computeRootLeftRightUp(init(p), init(left), init(right), f,  f(seed, last(right)));
            //  Prove that r1.0 == r
            calc == {
                r1.0;
                {  computeRootAndSiblingsIsCorrect(init(p),  init(left), init(right), f,  f(seed, last(right)),
                     init(valOnP)) ; }
                computeRootLeftRightUp(init(p),  init(left), init(right), f,  f(seed, last(right)));
                r;
            }
            (r, init(left) + [last(valOnP)])
        else      
            var r :=  computeRootAndLeftSiblingsUpOpt(
                    init(p), init(left), init(right), f, f(last(left), seed), init(valOnP));
                    (r.0, r.1 + [last(left)])
    }
 }