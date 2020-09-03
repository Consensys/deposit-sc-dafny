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

include "../intdiffalgo/DiffTree.dfy"

include "../trees/CompleteTrees.dfy"
include "../synthattribute/ComputeRootPath.dfy"
include "../helpers/Helpers.dfy"
include "../paths/PathInCompleteTrees.dfy"
include "../paths/NextPathInCompleteTreesLemmas.dfy"
include "../seqofbits/SeqOfBits.dfy"
include "../helpers/SeqHelpers.dfy"
include "../trees/Trees.dfy"

module CommuteProofs {

    import opened DiffTree

    import opened CompleteTrees
    import opened ComputeRootPath
    import opened Helpers
    import opened NextPathInCompleteTreesLemmas
    import opened PathInCompleteTrees
    import opened SeqOfBits
    import opened SeqHelpers
    import opened Trees 

    /**
     *  
     *  @param  p       A path.
     *  @param  b       Values of nodes on left of p.
     *  @param  seed    The new value for the leaf at p.
     */
    lemma {:induction p, b, seed} computeRootAndUpdateStateCommutes(p: seq<bit>, b : seq<int>, seed : int)
        requires 1 <= |p| == |b|
        ensures 
            var v1 := computeAllPathDiffUp(p, b, seed);
            var b' := computeLeftSiblingOnNextPathDep(p, b, seed);
                computeRootPathDiffUp(p, b', seed)
                == computeRootPathDiffUp(p, b, seed)
    {   //  Thanks Dafny
    }
    
    /**
     *  Compute the left siblings of nextPath from current values on left sibling.
     *
     *  @param  p       A path.
     *  @param  v2      The values of the nodes that are left siblings of nodes on the path.
     *  @param  seed    The value added to the leaf of the current path.
     *  @returns        The values of the nodes that are left siblings of nextPath(p).
     */
    function method computeLeftSiblingOnNextPathDep(p: seq<bit>, v2 : seq<int>, seed: int) : seq<int>
        requires 1 <= |p| 
        requires |v2| == |p|
        ensures computeLeftSiblingOnNextPathDep(p, v2, seed) ==
            var v1 := computeAllPathDiffUp(p, v2, seed);
            computeLeftSiblingOnNextPath(p, v1, v2)

        decreases p
    {
        if |p| == 1 then
            if first(p) == 0 then [seed] else v2 
        else 
            assert(|p| >= 2);
            if last(p) == 0 then 
                init(v2) + [diff(seed, 0)]
            else 
                assert(last(p) == 1);
                computeLeftSiblingOnNextPathDep(init(p), init(v2), diff(last(v2), seed)) + [last(v2)]
    } 

    /**
     *  Compute the left siblings of nextPath from current values on left sibling.
     *  Same version as before but mixing in k anf h.
     *
     *  @param  p       A path.
     *  @param  v2      The values of the nodes that are left siblings of nodes on the path.
     *  @param  seed    The value added to the leaf of the current path.
     *  @param  h       Size of p.
     *  @param  k       The number represented by p on h bits.
     *  @returns        The values of the nodes that are left siblings of nextPath(p).
     */
    function method computeLeftSiblingOnNextPathBridge(h : nat, k : nat, p: seq<bit>, v2 : seq<int>, seed: int) : seq<int>
        requires 1 <= |v2| == |p| == h

        requires k < power2(h)
        requires p == natToBitList2(k, h)

        ensures computeLeftSiblingOnNextPathBridge(h, k, p, v2, seed) ==
            var v1 := computeAllPathDiffUp(p, v2, seed);
            computeLeftSiblingOnNextPath(p, v1, v2)

        decreases p
    {
        if |p| == 1 then
            if first(p) == 0 then [seed] else v2 
        else 
            assert(|p| >= 2);
            assert(|p| == h);
            if last(p) == 0 then 
                assert(k % 2 == 0);
                init(v2) + [diff(seed, 0)]
            else 
                assert(last(p) == 1);
                assert(k % 2 == 1);
                computeLeftSiblingOnNextPathBridge(h - 1, k / 2, init(p), init(v2), diff(last(v2), seed)) + [last(v2)]
    } 

    //  Algorithms using k and h instead of the path p.

    /**
     *  Same version as before but without p.
     */
    function method computeLeftSiblingOnNextPathFinal(h : nat, k : nat, v2 : seq<int>, seed: int) : seq<int>
        requires 1 <= |v2| == h

        requires k < power2(h)

        ensures 
            var p := natToBitList2(k, h);
            var v1 := computeAllPathDiffUp(p, v2, seed);
                computeLeftSiblingOnNextPathBridge(h, k, p, v2, seed) 
                ==
                computeLeftSiblingOnNextPathFinal(h, k, v2, seed)

        decreases h
    {
        if h == 1 then
            if k % 2 == 0 then [seed] else v2 
        else 
            if k % 2 == 0 then 
                init(v2) + [diff(seed, 0)]
            else 
                computeLeftSiblingOnNextPathFinal(h - 1, k / 2, init(v2), diff(last(v2), seed)) + [last(v2)]
    } 
    
    /**
     *  The functional version of the deposit smart contract.
     */
    class Deposit {

        //  Versions of compute left siblings on compute root path using the
        //  height of the tree and the current leaf number



        /** The values on the left siblings of the path. */
        var left : seq<int>
    }

}