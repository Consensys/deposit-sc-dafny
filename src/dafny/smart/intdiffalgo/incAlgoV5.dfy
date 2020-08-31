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

include "IncAlgoV3.dfy"
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

/**
 *  Imperative version of algorithm.
 */
module IncAlgoV5 {
 
    import opened DiffTree
    import opened IncAlgoV3
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
     *  @todo: division by power2 computation is assumed. Prove it.
     */
    method merkleV1(h : nat, k : nat, valOnLeftAt : seq<int>, seed: int) 
                                                        returns (r : int, next: seq<int>)
        requires 1 <= h == |valOnLeftAt|
        requires k < power2(h)

        // ensures (r, next) == (computeRootPathDiffUp(natToBitList(k, h), valOnLeftAt, seed),
        //     computeLeftSiblingOnNextPath(natToBitList(k, h), computeAllPathDiffUp(natToBitList(k, h), valOnLeftAt, seed), valOnLeftAt)
        //     )

        // ensures (r, next) == computeRootPathDiffAndLeftSiblingsUpv4(h, k, valOnLeftAt, seed)
        // ensures r == computeRootPathDiffAndLeftSiblingsUpv4(h, k, valOnLeftAt, seed).0
    {
        var i := 0;
        var k' := k;

        r := seed ;
        next := [] ; 

        ghost var h1 := h;
        ghost var (r', next') := computeRootPathDiffAndLeftSiblingsUpv4c(h, k, valOnLeftAt, seed, []);

        //  need this fact to prove next assert
        assert(valOnLeftAt == valOnLeftAt[..h - i]);

        while (i < h)

            invariant 0 <= i <= h
            invariant i == |valOnLeftAt[.. i]|
            invariant 0 <= k' < power2(h1)
            invariant h1 == h - i
            invariant (r', next') == computeRootPathDiffAndLeftSiblingsUpv4c(h1, k', valOnLeftAt[..h1], r, next);


            decreases h - i 
        {
            if k' % 2 == 0 {
                next := [r] + next ;
                r := diff(r, 0);
            } else {
                next := [valOnLeftAt[h - i - 1]] + next ;
                r := diff(valOnLeftAt[h - i - 1], r);
            }
            //  the following is used to prove Inv4
            assert(valOnLeftAt[..h1 - 1] == valOnLeftAt[..h1][..h1 - 1]);
            i := i + 1;
            k' := k' / 2;
            h1 := h1 - 1;
        }
        //  after the loop we get the result
        assert(
            (r, next) // == (r', next')
            ==
            computeRootPathDiffAndLeftSiblingsUpv4c(h, k, valOnLeftAt, seed, [])
        );
    }

    lemma divIsZero(n : nat, m : nat) 
        requires n < m
        ensures n / m == 0 
    {

    }
 }