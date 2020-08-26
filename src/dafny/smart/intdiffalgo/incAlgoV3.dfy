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

include "IncAlgoV2.dfy"
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

module IncAlgoV3 {
 
    import opened DiffTree
    import opened IncAlgoV2
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
     *  Compute the root value and the left siblings of next path concurrently.
     */
    function  computeRootPathDiffAndLeftSiblingsUpv3(
        p : seq<bit>, 
        h : nat,
        k : nat,
        valOnLeftAt : seq<int>, seed: int) : (int, seq<int>)
        requires h == |p| == |valOnLeftAt| 
        requires |p| >= 1

        requires k < power2(|p|)
        requires natToBitList(k, |p|) == p
        
        /**
         *  V3 and V2 compute same result.
         */
        ensures computeRootPathDiffAndLeftSiblingsUpv3(p, h, k, valOnLeftAt, seed) ==
            computeRootPathDiffAndLeftSiblingsUpv2(p, valOnLeftAt, seed)

        decreases p
    {
     if |p| == 1 then
        assert( k == p[0] as nat);
        assert( h == |p|);
        var r := computeRootPathDiff(p, valOnLeftAt, seed);
        (r, if p[0] == 0 then [seed] else valOnLeftAt) 
    else 
        if p[|p| - 1] == 0 then
            assert( k % 2 == 0);
            assert( h == |p|);
            var r := computeRootPathDiffAndLeftSiblingsUpv3(
                        p[.. |p| - 1], 
                        h - 1,
                        k / 2,
                        valOnLeftAt[..|valOnLeftAt| - 1],   
                        diff(seed, 0) );
                    (r.0, valOnLeftAt[.. |valOnLeftAt| - 1] + [seed])
        else      
            assert( k % 2 == 1);
            assert( h == |p|);
            var r :=  computeRootPathDiffAndLeftSiblingsUpv3(
                    p[.. |p| - 1], 
                    h - 1,
                    k / 2,
                    valOnLeftAt[..|valOnLeftAt| - 1],  
                    diff(valOnLeftAt[|valOnLeftAt| - 1], seed));
                    /*  The last value [valOnLeftAt[|valOnLeftAt| - 1]] is not used on 
                        the next path as it is not a leftSibling of a node of next path.
                        at this level. As a consequence we can use any value to append to
                        the second component of the result .1. We just use the old value 
                        [valOnLeftAt[|valOnLeftAt| - 1] as it will enable us to "modify" 
                        in-place a unique array in the imperative version. */
                    (r.0, r.1 + [valOnLeftAt[|valOnLeftAt| - 1]])
    }

    /**
     *  Use the natural value of a path and height (supposedly of the tree) 
     *  to compute the results.
     */
    function method computeRootPathDiffAndLeftSiblingsUpv4(
        h : nat,
        k : nat,
        valOnLeftAt : seq<int>, seed: int) : (int, seq<int>)
        requires 1 <= h == |valOnLeftAt|
        requires k < power2(h)

        /**
         *  V4 and V3 compute same result.
         */
        ensures 
            computeRootPathDiffAndLeftSiblingsUpv4(h, k, valOnLeftAt, seed) ==
            var p := natToBitList(k, h);
            computeRootPathDiffAndLeftSiblingsUpv3(p, h, k, valOnLeftAt, seed) 

        decreases h
    {
        if h == 1 then
            var r := computeRootPathDiff([k as bit], valOnLeftAt, seed);
            assert(valOnLeftAt ==  [valOnLeftAt[0]]);
            (r, if k == 0 then [seed] else [valOnLeftAt[h - 1]]) 
        else 
            if k % 2 == 0 then
                var r := computeRootPathDiffAndLeftSiblingsUpv4(
                            h - 1,
                            k / 2,
                            valOnLeftAt[..h - 1],   
                            diff(seed, 0) );
                (r.0, valOnLeftAt[.. h - 1] + [seed])
            else      
                var r :=  computeRootPathDiffAndLeftSiblingsUpv4(
                        h - 1,
                        k / 2,
                        valOnLeftAt[..h - 1],  
                        diff(valOnLeftAt[h - 1], seed));
                        /*  The last value [valOnLeftAt[|valOnLeftAt| - 1]] is not used on 
                            the next path as it is not a leftSibling of a node of next path.
                            at this level. As a consequence we can use any value to append to
                            the second component of the result .1. We just use the old value 
                            [valOnLeftAt[|valOnLeftAt| - 1] as it will enable us to "modify" 
                            in-place a unique array in the imperative version. */
                (r.0, r.1 + [valOnLeftAt[h - 1]])
    }

    /**
     *  For path of size >= 2, computeRootPathDiffAndLeftSiblingsUp and computeRootPathDiffUp
     *  yield the same result.
     */
    lemma  computeRootAndSiblingsV4IsCorrect(h : nat,
        k : nat,
        valOnLeftAt : seq<int>, seed: int)
        requires 1 <= h == |valOnLeftAt|
        requires k < power2(h)

        ensures  computeRootPathDiffAndLeftSiblingsUpv4(h, k, valOnLeftAt, seed) == 
            (computeRootPathDiffUp(natToBitList(k, h), valOnLeftAt, seed),
            computeLeftSiblingOnNextPath(natToBitList(k, h), computeAllPathDiffUp(natToBitList(k, h), valOnLeftAt, seed), valOnLeftAt)
            )

    {   
        /*
         *  V4 computes same as V3, same as V2 and V2 is correct.
         */
        calc == {
            computeRootPathDiffAndLeftSiblingsUpv4(h, k, valOnLeftAt, seed);
            computeRootPathDiffAndLeftSiblingsUpv3(natToBitList(k, h), h, k, valOnLeftAt, seed);
            computeRootPathDiffAndLeftSiblingsUpv2(natToBitList(k, h), valOnLeftAt, seed);
            {
                computeRootAndSiblingsv2IsCorrect(natToBitList(k, h),  valOnLeftAt, seed);
            }
            (computeRootPathDiffUp(natToBitList(k, h), valOnLeftAt, seed),
            computeLeftSiblingOnNextPath(natToBitList(k, h), 
                computeAllPathDiffUp(natToBitList(k, h), valOnLeftAt, seed), valOnLeftAt));
        }   
    }

   /**
     *  Use the natural value of a path and height (supposedly of the tree) 
     *  to compute the results. Stop at h == 0 instead of h == 1. 
     */
    function method computeRootPathDiffAndLeftSiblingsUpv4b(
        h : nat,
        k : nat,
        valOnLeftAt : seq<int>, seed: int) : (int, seq<int>)
        requires 0 <= h == |valOnLeftAt|
        // requires h > 0 ==> k < power2(h)
        requires k < power2(h)

        decreases h
    {
        if h == 0 then
            (seed, [])
        else 
            if k % 2 == 0 then
                var r := computeRootPathDiffAndLeftSiblingsUpv4b(
                            h - 1,
                            k / 2,
                            valOnLeftAt[..h - 1],   
                            diff(seed, 0) );
                (r.0, valOnLeftAt[..h - 1] + [seed])
            else      
                var r :=  computeRootPathDiffAndLeftSiblingsUpv4b(
                        h - 1,
                        k / 2,
                        valOnLeftAt[..h - 1],  
                        diff(valOnLeftAt[h - 1], seed));
                        /*  The last value [valOnLeftAt[|valOnLeftAt| - 1]] is not used on 
                            the next path as it is not a leftSibling of a node of next path.
                            at this level. As a consequence we can use any value to append to
                            the second component of the result .1. We just use the old value 
                            [valOnLeftAt[|valOnLeftAt| - 1] as it will enable us to "modify" 
                            in-place a unique array in the imperative version. */
                (r.0, r.1 + [valOnLeftAt[h - 1]])
    }

    lemma  computeRootAndSiblingsV4bIsCorrect(h : nat,
        k : nat,
        valOnLeftAt : seq<int>, seed: int)
        requires 1 <= h == |valOnLeftAt|
        requires k < power2(h)

        ensures  computeRootPathDiffAndLeftSiblingsUpv4b(h, k, valOnLeftAt, seed) == 
           computeRootPathDiffAndLeftSiblingsUpv4(h, k, valOnLeftAt, seed)
    {
        if ( h >= 2 ) {
            //  if h >= 2 they compute exactly the same. Thanks Dafny
        } else {
            //  The only interesting case is h == 1
            //  If h == 1 then k == 0 or k == 1. We show that v4b computes same as v4
            //  by unfolding the computation.
            if (k % 2 == 0) {
                var r := computeRootPathDiffAndLeftSiblingsUpv4b(0, 0, [], diff(seed, 0));

                calc {
                    computeRootPathDiffAndLeftSiblingsUpv4b(h, k, valOnLeftAt, seed);
                    (r.0, valOnLeftAt[..h - 1] + [seed]);    
                    calc {
                        [] + [seed];
                        [seed];
                    }
                    (r.0, [seed]);
                    calc {
                        r.0;
                        diff(seed, 0);
                    }
                    (diff(seed, 0), [seed]);
                    (computeRootPathDiff([0], valOnLeftAt, seed), [seed]);
                }
                //  Thanks Dafny
            } else {
                //   k % 2 == 1 and k == 1
                var r := computeRootPathDiffAndLeftSiblingsUpv4b(0, 0, [], diff(valOnLeftAt[0], seed));
                calc {
                    computeRootPathDiffAndLeftSiblingsUpv4b(h, k, valOnLeftAt, seed);
                    (r.0, r.1 + [valOnLeftAt[h - 1]]);
                    calc {
                        r.1 + [valOnLeftAt[h - 1]];
                        [] + [valOnLeftAt[h - 1]];
                        [valOnLeftAt[h - 1]];
                    }
                    (r.0, [valOnLeftAt[h - 1]]);
                    (diff(valOnLeftAt[h - 1], seed), [valOnLeftAt[h - 1]]);
                    (computeRootPathDiff([1], valOnLeftAt, seed),  [valOnLeftAt[h - 1]]);
                }
            }
        }
    }

    /**
     *  Tail recursive version of algorithm.
     */
    function method computeRootPathDiffAndLeftSiblingsUpv4c(
        h : nat,
        k : nat,
        //  ghost z : nat,  //  make sure we propagate the initial value of height 
                        //  to prove that Inv0 holds
        valOnLeftAt : seq<int>, 
        seed: int,
        newLeft : seq<int>) : (int, seq<int>)
        requires 0 <= h == |valOnLeftAt|
        // requires h > 0 ==> k < power2(h)
        // requires |valOnLeftAt| + |newLeft| == z //  Inv0
        requires k < power2(h)

        // requires z == h

        decreases h
    {
        if h == 0 then
            (seed, newLeft)
        else 
            if k % 2 == 0 then
                // assert(|valOnLeftAt[..h - 1]| + |[seed]| + |newLeft| == h);
                computeRootPathDiffAndLeftSiblingsUpv4c(
                            h - 1,
                            k / 2,
                            // z,
                            valOnLeftAt[..h - 1],   
                            diff(seed, 0),
                            [seed] + newLeft)
            else      
                computeRootPathDiffAndLeftSiblingsUpv4c(
                        h - 1,
                        k / 2,
                        // z,
                        valOnLeftAt[..h - 1],  
                        diff(valOnLeftAt[h - 1], seed),
                        [valOnLeftAt[h - 1]] + newLeft)
                        /*  The last value [valOnLeftAt[|valOnLeftAt| - 1]] is not used on 
                            the next path as it is not a leftSibling of a node of next path.
                            at this level. As a consequence we can use any value to append to
                            the second component of the result .1. We just use the old value 
                            [valOnLeftAt[|valOnLeftAt| - 1] as it will enable us to "modify" 
                            in-place a unique array in the imperative version. */
    }

     lemma  {:induction h} computeRootAndSiblingsV4cIsCorrect(h : nat,
        k : nat,
        // z : nat,
        valOnLeftAt : seq<int>, seed: int,  newLeft : seq<int>)
        requires 1 <= h == |valOnLeftAt|
        requires k < power2(h)
        requires |valOnLeftAt| + |newLeft| == h - 1

        // ensures |computeRootPathDiffAndLeftSiblingsUpv4c(h, k, valOnLeftAt, seed, []).1| == h

        ensures  computeRootPathDiffAndLeftSiblingsUpv4b(h, k, valOnLeftAt, seed) == 
           computeRootPathDiffAndLeftSiblingsUpv4c(h, k, valOnLeftAt, seed, [])

        ensures computeRootPathDiffAndLeftSiblingsUpv4b(h, k, valOnLeftAt, seed) ==
            (computeRootPathDiffUp(natToBitList(k, h), valOnLeftAt, seed),
            computeLeftSiblingOnNextPath(natToBitList(k, h), computeAllPathDiffUp(natToBitList(k, h), valOnLeftAt, seed), valOnLeftAt)
            )

    {   
        //  Thanks Dafny
    }
 }