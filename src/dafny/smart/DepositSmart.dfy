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

include "./synthattribute/RightSiblings.dfy"
include "./helpers/Helpers.dfy"
include "./helpers/SeqHelpers.dfy"
include "./paths/PathInCompleteTrees.dfy"
include "./seqofbits/SeqOfBits.dfy"
include "./trees/MerkleTrees.dfy"
include "./algorithms/IndexBasedAlgorithm.dfy"

/**
 *  A proof of correctness for the Deposit Smart Contract Algorithm
 *  with dynamuc allocation of arrays.
 *  This proof takes into account the allocations of arrays on the heap
 *  and uses the Dafny dynamic frames support to reason about the
 *  memory footprint (and to prove that no overwriting of array elements occur.)
 *  
 */
module DepositSmart {

    import opened RSiblings
    import opened Helpers
    import opened SeqHelpers
    import opened PathInCompleteTrees
    import opened SeqOfBits
    import opened MerkleTrees
    import opened IndexBasedAlgorithm

    /**
     *  Provide deposit smart contract algorithms.
     *
     *  The autocontracts attribute generate some boilerplate 
     *  code in the constructor and the methods. It also
     *  implicitely adds to each method Valid() as a pre and
     *  post-condition.
     */
    class {:autocontracts} Deposit {

        //  State Variables.

        /** The default value for the leaves of the tree. It is 0 in the orginal algorithm. */
        const d : int 

        /** The attribute function to synthesise. Hash funciton in the original algorithm. */
        const f : (int, int) -> int
    
        /** The height of the tree. */
        const TREE_HEIGHT : nat

        /** branch is rBranch (see after) in reverse order. */
        var branch: array<int>

        /** zero_hashes is zero_h (see below) in reverse order. */
        const zero_hashes: array<int> 

        /** The number of values added to the list. Also the index of the next available leaf. */
        var count : nat 

        //  Ghost variables used for the correctness proof.

        /** The values on the left siblings of the path to leaf at index k. */
        ghost var rBranch : seq<int>

        /** The values of the right siblings of the path to leaf at index k. */
        ghost const zero_h : seq<int>

        /** The list of values added so far. */
        ghost var values : seq<int> 

        //  Property to maintain to ensure correctness.

        /** 
         *  @note   `values` record the values added so far. buildMerkle(values, TREE_HEIGHT, f, d)
         *          is the Merkle tree that corresponds to the list `values`.
         *          `rBranch` and `zero_h` should always contain the left (resp. right) siblings 
         *          of the path to the |values|-th leaf in the Merkle tree. 
         *  @note   |values| is the length of the list `values`.
         */
        predicate Valid()
        {
            //  Constraints on height and length of lists.
            1 <= TREE_HEIGHT == branch.Length == |rBranch| == |zero_h| 
            && branch[..] == reverse(rBranch)
            //  Maximum number of values stored in the tree bounded.
            && count < power2(TREE_HEIGHT) 
            //  count is the number of values added so far and should correspond to |values|.
            && |values| == count
            //  the pointers to the arrays are distinct
            && zero_hashes != branch
            //  zero_h is constant and equal to default values for each level of t.
            && zero_h == zeroes(f, d, TREE_HEIGHT - 1)
            && zero_hashes[..] == reverse(zero_h)
            //  rBranch and zero_h are the left and right siblings of path to 
            //  |values|-th leaf in buildMerkle(values, TREE_HEIGHT, f, d)
            && areSiblingsAtIndex(|values|, buildMerkle(values, TREE_HEIGHT, f, d), rBranch, zero_h)
        }

        /**
         *  Initialisation.
         *
         *  @param  h       The height of the tree.
         *  @param  f1      The function used to decorate the tree (e.g. hash).
         *  @param  default The default value of the leaves in the tree.
         *
         *  @note           The initial value of `rBranch` is unconstrained (apart the length
         *                  that should be the same as `h`). This implies that the algorithms
         *                  are correct given any initial values for `rBranch`.
         *  @note           The autocontracts attribute ensures that the post condition
         *                   Valid() holds after the initilisation.
         */
        constructor(h: nat, l : seq<int>, f1 : (int, int) -> int, default : int) 
            requires h >= 1
            requires |l| == h 
            ensures branch != zero_hashes
            ensures count == 0
            ensures TREE_HEIGHT == h 
        {
            //  State variables
            //  Due to a bug (Issue #1111) in Dafny 3.0.0 in the translation
            //  of concurrent assignments for consts, we initialise them one by one.
            // TREE_HEIGHT, count, f, d := h, 0, f1, default;
            TREE_HEIGHT := h;
            count := 0;
            f := f1;
            d := default;

            //  Allocate the array branch, and initialise with `l`.
            branch := new int[h](i requires 0 <= i < h => l[i]);

            // Allocate the zeroes array.
            zero_hashes := new int[h](i requires 0 <= i < h  => zeroes(f1, default, h - 1)[h - 1 - i]);
    
            //  Ghost variables
            zero_h, rBranch := zeroes(f1, default, h - 1), reverse(l) ;
            values := [];

            //  Proof that right siblings of path natToBitList2(0, h) are zero_h.
            bitToNatToBitsIsIdentity(0, h);
            valueIsZeroImpliesAllZeroes(natToBitList2(0, h));
            leafAtPathIsIntValueOfPath(natToBitList2(0, h), buildMerkle([], h, f1, default), 0, 0);
            rightSiblingsOfLastPathAreDefault(natToBitList2(0, h), buildMerkle([], h, f1, default), 0, f1, 0, default);
        }

        ///////////////////////////////////////////////////////////////////////////
        //  Imperative versions of algorithms with dynamic array allocations.
        ///////////////////////////////////////////////////////////////////////////

        /**
         *  This method initialises the array zero_hashes.
         *  The autocintracts proof implies:
         *  1. whenever init_zero_hashes() is called, Valid() holds
         *  2. it follows that it holds if the initilisation happens right after
         *      the constructor or at any other time later.
         */
        method init_zero_hashes()
            modifies this.zero_hashes
        {
            assert(zero_hashes.Length >= 1);
            var i := 0 ;
            zero_hashes[0] := d;
            while i < zero_hashes.Length - 1 
                invariant 0 <= i <=  zero_hashes.Length - 1
                invariant zero_hashes[..i + 1] == reverse(zero_h)[..i + 1]

                decreases zero_hashes.Length - i
            {
                zero_hashes[i + 1] := f(zero_hashes[i], zero_hashes[i]);
                i := i + 1;
            }

            //  Invariant for i == zero_hashes.Length - 1
            assert(zero_hashes[..] == reverse(zero_h));

        }

       
        /** 
         *  This method updates the left siblings (rBranch) in order
         *  to maintain the correspondence with the Merkle tree for values.
         *  This is captured by the Valid() predicate.
         *  
         *  @param  v   The new deposit amount.
         *
         *  @note       The autocontracts attribute impliictely adds the pre and 
         *              post condition Valid() to the spec of each method.
         *  
         */
        method {:timeLimitMultiplier 10} deposit(v : int) 
            /** The tree cannot be full.  */
            requires count < power2(TREE_HEIGHT) - 1     
            /** The new value `v` should be added to history of received values. */
            ensures values == old(values) + [v]    
            // ensures count == old(count) + 1
            // ensures TREE_HEIGHT == old(TREE_HEIGHT)
            
            modifies this, this.branch
        {
            var value := v;
            var size : nat := count;
            var i : nat := 0;
            
            //  Store the expected result in e.
            ghost var e := computeLeftSiblingsOnNextpathWithIndex(TREE_HEIGHT, old(size), old(rBranch), zero_h, f, v);
           
            //  rBranch and zero_h correspond to the vectors branch and zero_hashes in reverse
            //  order, so the index TREE_HEIGHT - i - 1 is used in place if i to dereference them.
            while size % 2 == 1 

                invariant 0 <= TREE_HEIGHT - i - 1 < |rBranch| == branch.Length
                invariant 0 <= size < power2(TREE_HEIGHT - i) - 1
                
                //  Main invariant:
                invariant e == 
                    computeLeftSiblingsOnNextpathWithIndex(
                        TREE_HEIGHT - i, size, 
                        take(rBranch, TREE_HEIGHT - i), 
                        take(zero_h, TREE_HEIGHT - i), f, value) 
                    + drop(rBranch, TREE_HEIGHT - i)     //  proving the + may need sone help

                //  Termination is easy as size decreases and must be zero.
                decreases size 
            {
                //  The proof steps for the main invariant.
                calc == {
                    e;
                    computeLeftSiblingsOnNextpathWithIndex(
                        TREE_HEIGHT - i, size, 
                        take(rBranch, TREE_HEIGHT - i), 
                        take(zero_h, TREE_HEIGHT - i), f, value) 
                    + drop(rBranch, TREE_HEIGHT - i);
                    { 
                        assert(size < power2(TREE_HEIGHT));
                        mainInvariantProofHelper(TREE_HEIGHT - i, size, rBranch, zero_h, f, value); 
                    }
                    computeLeftSiblingsOnNextpathWithIndex(
                        TREE_HEIGHT - i - 1, size / 2, 
                        take(rBranch, TREE_HEIGHT - i - 1), 
                        take(zero_h, TREE_HEIGHT - i - 1), f,  f(rBranch[TREE_HEIGHT - i - 1], value)) 
                    + drop(rBranch, TREE_HEIGHT - i - 1);
                }

                // Algorithm
                value := f(branch[i], value);
                size := size / 2;
                i := i + 1;
            }
            //  Show that e == rBranch[TREE_HEIGHT - i - 1 := value]
            calc == {
                e;
                computeLeftSiblingsOnNextpathWithIndex(
                        TREE_HEIGHT - i, size, 
                        take(rBranch, TREE_HEIGHT - i), 
                        take(zero_h, TREE_HEIGHT - i), f, value) 
                    + drop(rBranch, TREE_HEIGHT - i);
                calc == {
                    computeLeftSiblingsOnNextpathWithIndex(
                        TREE_HEIGHT - i, size, 
                        take(rBranch, TREE_HEIGHT - i), 
                        take(zero_h, TREE_HEIGHT - i), f, value) ;
                    { assert(size % 2 == 0 && TREE_HEIGHT - i - 1 >= 0 ); }
                    init(take(rBranch, TREE_HEIGHT - i)) + [value];
                }
                init(take(rBranch, TREE_HEIGHT - i)) + [value] + drop(rBranch, TREE_HEIGHT - i);
                { updateAndsplitSeqAtIndex(rBranch, value, TREE_HEIGHT - i);} 
                rBranch[TREE_HEIGHT - i - 1 := value];
                old(rBranch)[TREE_HEIGHT - i - 1 := value];
            }
            //  This is the important hidden property: 0 <= TREE_HEIGHT - i - 1 < |rBranch|
            //  and also 0 <= i < brancvh.Lenhth 
            //  This proves that in the original version, i is NEVER out of range, 
            //  and always in [0, branch.Lenhth[
            rBranch := rBranch[TREE_HEIGHT - i - 1 := value];

            //  if follows that 0 <= i < |branch| and no index-out-of-bounds
            branch[i] := value;

            //  Some hints for the proof of the post conditions.
            assert(rBranch == old(rBranch)[TREE_HEIGHT - i - 1 := value] == e);
            assert(branch[..] == old(branch)[..][i := value]);
            assert(branch[..] == reverse(rBranch));

            //  Finally increment count. Note that count can be incremented at the beginning
            //  provided that the while loop condition is flipped to sizeA % 2 == 0.
            count := count + 1;

            //  Update (ghost) values
            values := values + [v];
           
            assert(count == old(count) + 1 == |values| == |old(values)| + 1);
            computeNewLeftIsCorrect(old(values), v, TREE_HEIGHT, old(rBranch), zero_h, f, d);
            assert(areSiblingsAtIndex(|values|, buildMerkle(values, TREE_HEIGHT, f, d), rBranch, zero_h));
        }

        /**
         *  Split a seq with take/drop at a given index and update.
         */
        lemma updateAndsplitSeqAtIndex<T>(s: seq<T>, v: T, i: nat) 
            requires |s| >= 1
            requires 1 <= i <= |s|
            ensures s[i - 1:= v] == init(take(s,i)) + [v] + drop(s, i)
        {   //  Thanks Dafny 
        }

        /**
         *  Equality of computations used to prove the main invariant 
         *  of deposit. 
         */
        lemma {:induction false} mainInvariantProofHelper(h: nat, k : nat, left : seq<int>, right : seq<int>, f : (int, int) -> int, seed: int)
            requires 1 <= h <= |left| == |right| 
            // requires 0 < k < power2(h) 
            requires k < power2(h) 
            requires k % 2 == 1
            ensures k / 2 < power2(h - 1)
            ensures computeLeftSiblingsOnNextpathWithIndex(
                        h, k, 
                        take(left, h), 
                        take(right, h), f, seed) 
                    + drop(left, h) 
                    == computeLeftSiblingsOnNextpathWithIndex(
                        h - 1, k / 2 , 
                        take(left, h - 1), 
                        take(right, h - 1), f,  f(left[h - 1], seed)) 
                    + drop(left, h - 1)
        {
            power2Div2LessThan(k, h);
            calc == {
                computeLeftSiblingsOnNextpathWithIndex(
                    h, k, 
                    take(left, h), 
                    take(right, h), f, seed) 
                + drop(left, h);
                calc == {
                    computeLeftSiblingsOnNextpathWithIndex(
                        h, k, 
                        take(left, h), 
                        take(right, h), f, seed) ;
                    { assert(k % 2 == 1 && h > 0 ); }
                    computeLeftSiblingsOnNextpathWithIndex(
                        h - 1, k / 2 , 
                        init(take(left, h)), 
                        init( take(right, h)), f,  f(last(take(left, h)), seed)) + [last(take(left, h))];
                    { seqIndexLemmas(left, h); seqIndexLemmas(right, h); }
                    computeLeftSiblingsOnNextpathWithIndex(
                        h - 1, k / 2 , 
                        take(left, h - 1), 
                        take(right, h - 1), f,  f(left[h - 1], seed)) + [left[h - 1]];
                }
                computeLeftSiblingsOnNextpathWithIndex(
                    h - 1, k / 2 , 
                    take(left, h - 1), 
                    take(right, h - 1), f,  f(left[h - 1], seed)) + [left[h - 1]] 
                + drop(left, h);
            }
        }

        /**
         *  The get_deposit_root() function.
         *
         *  This method should always return the root value of the tree.
         *
         *  @returns    The root value of the Merkle Tree for values.
         *
         *  @note       The autocontracts attribute impliictely adds the pre and 
         *              post condition Valid() to the spec of each method.
         */
        method {:timeLimitMultiplier 8} get_deposit_root() returns (r : int) 
            /** The result of get_deposit_root_() is the root value of the Merkle tree for values.  */
            ensures r == buildMerkle(values, TREE_HEIGHT, f, d).v 
        {
            //  Store the expected result in a ghost variable.
            ghost var e := computeRootLeftRightUpWithIndex(TREE_HEIGHT, count, rBranch, zero_h, f, d);

            //  Start with default value for r.
            r := d;
            var h := 0;
            var size := count;

            while h < TREE_HEIGHT
            
                //  no out of range in seqs:
                invariant 0 <= h <= TREE_HEIGHT
                invariant 0 <= size < power2(TREE_HEIGHT - h)
                //  Main invariant:
                invariant e == 
                    computeRootLeftRightUpWithIndex(
                        TREE_HEIGHT - h, size, 
                        take(rBranch, TREE_HEIGHT - h), take(zero_h, TREE_HEIGHT - h), f, r)

                decreases TREE_HEIGHT - h 
            {
                //  A little help for Dafny to check the proof of the main invariant
                assert(last(take(rBranch, TREE_HEIGHT - h)) == rBranch[TREE_HEIGHT - h - 1]);
                assert(last(take(zero_h, TREE_HEIGHT - h)) == zero_h[TREE_HEIGHT - h - 1]);
                assert(init(take(rBranch, TREE_HEIGHT - h)) == take(rBranch, TREE_HEIGHT - h - 1));
                assert(init(take(zero_h, TREE_HEIGHT - h)) == take(zero_h, TREE_HEIGHT - h - 1));

                //  Algorithm 
                if size % 2 == 1 {
                    assert(rBranch[TREE_HEIGHT - h - 1] == branch[h]);
                    r := f(branch[h], r);
                } else {
                    assert(zero_hashes[h] ==  zero_h[TREE_HEIGHT - h - 1]);
                    r := f(r, zero_hashes[h]);
                }
                size := size / 2;
                h := h + 1;
            }

            //  By invariant at the end of the loop and definition of computeRootLeftRightUpWithIndex
            assert(e == computeRootLeftRightUpWithIndex(0, 0, [], [], f, r) == r);

            //  The proof of post condition follows easily from:
            computeRootIsCorrect(values, TREE_HEIGHT, rBranch, zero_h, f, d);
        }

    }
}