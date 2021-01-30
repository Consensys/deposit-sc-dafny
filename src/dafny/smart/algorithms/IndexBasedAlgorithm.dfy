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

include "OptimalAlgorithm.dfy"
include "../trees/CompleteTrees.dfy"
include "../synthattribute/ComputeRootPath.dfy"
include "../helpers/Helpers.dfy"
include "../paths/PathInCompleteTrees.dfy"
include "../paths/NextPathInCompleteTreesLemmas.dfy"
include "../seqofbits/SeqOfBits.dfy"
include "../helpers/SeqHelpers.dfy"
include "../trees/Trees.dfy"

/**
 *  Optimal algorithm using the index of leaf and height of the tree rather than 
 *  a sequence of bits for the path.
 */
module IndexBasedAlgorithm {
 
    import opened OptimalAlgorithm
    import opened CompleteTrees
    import opened ComputeRootPath
    import opened Helpers
    import opened PathInCompleteTrees
    import opened NextPathInCompleteTreesLemmas
    import opened SeqOfBits
    import opened SeqHelpers
    import opened Trees

    ///////////////////////////////////////////////////////////////////////////
    //  Main algorithms
    ///////////////////////////////////////////////////////////////////////////

     /**
     *  This version switches to `computeRootLeftRightUpWithIndex` only as soon as 
     *  we encounter a path p such that last(p) == 0.
     *  Moreover the base case is for h == 0 rather 1.
     *
     *  @param  h           Height of the tree.
     *  @param  k           Index of leaf in the tree.
     *  @param  left        The values of the left siblings of nodes on path `p`.
     *  @param  right       The values of the left siblings of nodes on path `p`.
     *  @param  seed        The value at nodeAt(p).
     *  @param  f           The binary operation to compute.
     */
    function computeRootAndLeftSiblingsWithIndex<T>(
        h : nat, k : nat, left : seq<T>, right : seq<T>, f : (T, T) -> T, seed: T) : (T, seq<T>)
        requires |left| == |right| == h
        requires k < power2(h) 

        decreases h 
    {
        if h == 0 then
            (seed, []) 
        else 
            // pre-condition for recursive call is satisfied.
            power2Div2LessThan(k, h);
            assert(k / 2 < power2(h - 1));
            if k % 2 == 0 then
                var x := computeRootLeftRightUpWithIndex(h - 1, k / 2, init(left), init(right), f,  f(seed, last(right)));
                (x, init(left) + [seed])
            else      
                var r :=  computeRootAndLeftSiblingsWithIndex(
                    h - 1, k / 2, init(left), init(right), f, f(last(left), seed));
                (r.0, r.1 + [last(left)])
    }

     /**  
     *  Compute the root value on a path bottom up using index instead of path.
     *  
     *  @param  h       A length (the height of the tree in the problem).
     *  @param  k       An index.
     *  @param  left    The value of `f` on each left sibling.
     *  @param  right   The value of `f` on each right sibling.
     *  @param  f       The binary operation to compute.
     *  @param  seed    The value at the end of the path.
     *
     *  @note           The correctness proof is by induction. The only 
     *                  hint needed is that the pre-condition for the recursive call is satisfied.
     * 
     */
    function method computeRootLeftRightUpWithIndex<T>(h : nat, k : nat, left : seq<T>, right: seq<T>, f : (T, T) -> T, seed: T) : T
        requires |left| == |right| == h
        requires k < power2(h)

        ensures computeRootLeftRightUpWithIndex(h, k, left, right, f, seed)  == 
            computeRootLeftRightUp(natToBitList2(k, h), left, right, f, seed)

        decreases h 
    {
        if h == 0 then
            seed 
        else 
            // Hint for the correctness proof: pre-condition for recursive call is satisfied.
            power2Div2LessThan(k, h);
            assert(k / 2 < power2(h - 1));
            computeRootLeftRightUpWithIndex(
                h - 1, k / 2, init(left), init(right), f,
                    if k % 2 == 0 then f(seed, last(right)) else f(last(left), seed)
            )
    }

    ///////////////////////////////////////////////////////////////////////////
    //  Main lemma.
    ///////////////////////////////////////////////////////////////////////////
    /**
     *  We can compute the result with base case 0 and it is correct for
     *  tree of height >= 1.
     *
     *  @param  h       A length (the height of the tree in the problem).
     *  @param  k       An index.
     *  @param  left    The value of `f` on each left sibling.
     *  @param  right   The value of `f` on each right sibling.
     *  @param  f       The binary operation to compute.
     *  @param  seed    The value at the end of the path.
     */
    lemma {:induction h} computeWithIndexFromZeroIsCorrect<T>(
        h : nat, k : nat, left : seq<T>, right : seq<T>, f : (T, T) -> T, seed: T)
        requires 1 <= |left| == |right| == h
        requires k < power2(h) 
        ensures computeRootAndLeftSiblingsWithIndex(h, k, left, right, f, seed) == 
            computeRootAndLeftSiblingsWithIndex1(h, k, left, right, f, seed)
        decreases h 
    {
        if h == 1 {
            reveal_power2();
            if k % 2 == 0 {
                //  Thanks
            } else {
                assert(k == 1);
                var r :=  computeRootAndLeftSiblingsWithIndex(
                    h - 1, k / 2, init(left), init(right), f, f(last(left), seed));
                calc == {
                    r;
                    (f(last(left), seed), []);
                }
                calc == {
                    computeRootAndLeftSiblingsWithIndex(h, k, left, right, f, seed);
                    (f(last(left), seed), [] + [last(left)]);
                    calc == {
                        [] + [last(left)];
                        [last(left)];
                    }
                    (f(last(left), seed), [last(left)]);
                }
            }
        } else {
            power2Div2LessThan(k, h);
            assert(k / 2 < power2(h - 1));
            var x := if k % 2 == 0 then f(seed, last(right)) else f(last(left), seed);
            computeWithIndexFromZeroIsCorrect(h - 1, k / 2, init(left), init(right), f, x);
        }
    }

    ///////////////////////////////////////////////////////////////////////////
    //  Helper functions.
    ///////////////////////////////////////////////////////////////////////////

    /**
     *  This version switches to `computeRootLeftRightUpWithIndex` only as soon as 
     *  we encounter a path p such that last(p) == 0.
     *
     *  @param  h           Height of the tree.
     *  @param  k           Index of leaf in the tree.
     *  @param  left        The values of the left siblings of nodes on the path to `k`-th leaf.
     *  @param  right       The values of the left siblings of nodes on the path to `k`-th leaf.
     *  @param  seed        The value at nodeAt(p).
     *  @param  f           The binary operation to compute.
     */
    function computeRootAndLeftSiblingsWithIndex1<T>(
        h : nat, k : nat, left : seq<T>, right : seq<T>, f : (T, T) -> T, seed: T) : (T, seq<T>)
        requires 1 <= |left| == |right| == h
        requires k < power2(h) 

        /** Special case for h == 1. */
        ensures h == 1 && k % 2 == 0 ==> 
            computeRootAndLeftSiblingsWithIndex1(h, k, left, right, f, seed) == (f(seed, last(right)), [seed])
         ensures h == 1 && k % 2 == 1 ==> 
            computeRootAndLeftSiblingsWithIndex1(h, k, left, right, f, seed) == (f(last(left), seed), [last(left)])

        ensures 
            computeRootAndLeftSiblingsWithIndex1(h, k, left, right, f, seed)
            == 
            computeRootAndLeftSiblingsUpOpt(natToBitList2(k, h), left, right, f, seed)

        decreases h 
    {
        if h == 1 then
            assert(left == [last(left)]);
            var r := computeRootLeftRightUpWithIndex(h, k, left, right, f, seed);
            (r, if k % 2 == 0 then [seed] else left) 
        else 
            // Hint for the correctness proof: pre-condition for recursive call is satisfied.
            power2Div2LessThan(k, h);
            assert(k / 2 < power2(h - 1));
            if k % 2 == 0 then
                var x := computeRootLeftRightUpWithIndex(h - 1, k / 2, init(left), init(right), f,  f(seed, last(right)));
                (x, init(left) + [seed])
            else      
                var r :=  computeRootAndLeftSiblingsWithIndex1(
                    h - 1, k / 2, init(left), init(right), f, f(last(left), seed));
                (r.0, r.1 + [last(left)])
    }

     /**
     *  Compute the left siblings on next path using index and base cas eis h == 0.
     *
     *  @param  h           Height of the tree.
     *  @param  k           Index of leaf in the tree.
     *  @param  left        The values of the left siblings of nodes on the path to `k`-th leaf.
     *  @param  right       The values of the left siblings of nodes on the path to `k`-th leaf.
     *  @param  seed        The value at nodeAt(p).
     *  @param  f           The binary operation to compute.
     *  @returns            The values of the left siblings on the next path.
     *
     */
    function method computeLeftSiblingsOnNextpathWithIndex<T>(
        h : nat, k : nat, left : seq<T>, right : seq<T>, f : (T, T) -> T, seed: T) : seq<T>
        requires |left| == |right| == h
        requires k < power2(h) 

        ensures h >= 1 ==>
            computeLeftSiblingsOnNextpathWithIndex(h, k, left, right, f, seed)
            == 
            computeRootAndLeftSiblingsWithIndex(h, k, left, right, f, seed).1
            == 
            computeLeftSiblingOnNextPathFromLeftRight(natToBitList(k, h), left, right, f, seed)

        decreases h 
    {
        if h == 0 then
            []
        else 
            computeWithIndexFromZeroIsCorrect(h, k, left, right, f, seed);
            // Hint for the correctness proof: pre-condition for recursive call is satisfied.
            power2Div2LessThan(k, h);
            assert(k / 2 < power2(h - 1));
            if k % 2 == 0 then
                init(left) + [seed]
            else      
                var r :=  computeLeftSiblingsOnNextpathWithIndex(
                    h - 1, k / 2, init(left), init(right), f, f(last(left), seed));
                r + [last(left)]
    }

 }