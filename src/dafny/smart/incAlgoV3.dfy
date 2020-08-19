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

include "IncAlgoV2.dfy"
include "CompleteTrees.dfy"
include "ComputeRootPath.dfy"
include "GenericComputation.dfy"
include "Helpers.dfy"
include "MerkleTrees.dfy"
include "NextPathInCompleteTreesLemmas.dfy"
include "PathInCompleteTrees.dfy"
include "SeqOfBits.dfy"
include "Trees2.dfy"

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
     *  Compute the root value and the left siblings concurrently.
     *  The fact that this version and the non-optimised (V1)
     *  computeRootPathDiffAndLeftSiblingsUp computes the same result is
     *  provided by lemma v1Equalsv2.
     */
   function computeRootPathDiffAndLeftSiblingsUpv3(
        p : seq<bit>, 
        h : nat,
        k : nat,
        valOnLeftAt : seq<int>, seed: int) : (int, seq<int>)
        requires h == |p| == |valOnLeftAt| 
        requires |p| >= 1

        requires k < power2(|p|)
        requires natToBitList(k, |p|) == p
        
        /**
         *  V3 and V2 computes same result.
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

     function computeRootPathDiffAndLeftSiblingsUpv4(
        h : nat,
        k : nat,
        valOnLeftAt : seq<int>, seed: int) : (int, seq<int>)
        requires 1 <= h == |valOnLeftAt|
        requires k < power2(h)

        /**
         *  V4 and V3 computes same result.
         */
        ensures computeRootPathDiffAndLeftSiblingsUpv4(h, k, valOnLeftAt, seed) ==
            computeRootPathDiffAndLeftSiblingsUpv3(natToBitList(k, h), h, k, valOnLeftAt, seed) 

        decreases h
    {
    if h == 1 then
        var r := computeRootPathDiff([k as bit], valOnLeftAt, seed);
        (r, if k == 0 then [seed] else valOnLeftAt) 
    else 
        if k % 2 == 0 then
            var r := computeRootPathDiffAndLeftSiblingsUpv4(
                        h - 1,
                        k / 2,
                        valOnLeftAt[..|valOnLeftAt| - 1],   
                        diff(seed, 0) );
                    (r.0, valOnLeftAt[.. |valOnLeftAt| - 1] + [seed])
        else      
            var r :=  computeRootPathDiffAndLeftSiblingsUpv4(
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

 }