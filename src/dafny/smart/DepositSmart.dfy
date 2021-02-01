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

include "./synthattribute/ComputeRootPath.dfy"
include "./synthattribute/RightSiblings.dfy"
include "./helpers/Helpers.dfy"
include "./helpers/SeqHelpers.dfy"
include "./paths/PathInCompleteTrees.dfy"
include "./paths/NextPathInCompleteTreesLemmas.dfy"
include "./seqofbits/SeqOfBits.dfy"
include "./trees/Trees.dfy"
include "./trees/MerkleTrees.dfy"
include "./algorithms/IndexBasedAlgorithm.dfy"

/**
 *  A proof of correctness for the Deposit Smart Contract Algorithm.
 *  
 */
module DepositSmart {

    import opened ComputeRootPath
    import opened RSiblings
    import opened Helpers
    import opened SeqHelpers
    import opened NextPathInCompleteTreesLemmas
    import opened PathInCompleteTrees
    import opened SeqOfBits
    import opened Trees 
    import opened MerkleTrees
    import opened IndexBasedAlgorithm

    /**
     *  Provide deposit smart contract algorithms.
     */
    class Deposit {

        //  State Variables.

        /** The default value for the leaves. It is 0 in the orginal algorithm. */
        const d : int 

        /** The attribute function to synthesise. Hash funciton in the original algorithm. */
        const f : (int, int) -> int
    
        /** The height of the tree. */
        const TREE_HEIGHT : nat

        /** The values on the left siblings of the path to leaf at index k. */
        var branch : seq<int>

        /** The values of the right siblings of the path to leaf at index k. */
        const zero_h : seq<int>

        /** The number of values added to the list. Also the index of the next available leaf. */
        var count : nat 

        //  Ghost variables used for the correctness proof.

        /** The list of values added so far. */
        ghost var values : seq<int> 

        //  Property to maintain to ensure correctness.

        /** 
         *  @note   `values` record the values added so far. buildMerkle(values, TREE_HEIGHT, f, d)
         *          is the Merkle tree that corresponds to `values`.
         *          `branch` and `zero_h` should always contain the left (resp. right) siblings 
         *          of the path to the |values|-th leaf in the Merkle tree. 
         *  @note   |values| is the length of the
         *          list `values`.
         */
        predicate Valid()
            reads this
        {
            //  Constraints on height and length of lists.
            1 <= TREE_HEIGHT == |branch| == |zero_h| 
            //  Maximum number of values stored in the tree bounded.
            && count < power2(TREE_HEIGHT) 
            //  count is the number of values added so far and should correspond to |values|.
            && |values| == count
            //  zero_h is constant and equal to default values for each level of t.
            && zero_h == zeroes(f, d, TREE_HEIGHT - 1)
            //  branch and zero_h are the left and right siblings of path to 
            //  |values|-th leaf in buildMerkle(values, TREE_HEIGHT, f, d)
            && areSiblingsAtIndex(|values|, buildMerkle(values, TREE_HEIGHT, f, d), branch, zero_h)
        }

        /**
         *  Initialisation.
         *
         *  @param  h       The height of the tree.
         *  @param  f1      The function used to decorate the tree (e.g. hash).
         *  @param  default The default value of the leaves in the tree.
         *
         *  @note           The initial value of `branch` is unconstrained (apart the length
         *                  that should be the same as `h`). This implies that the algorithms
         *                  are correct given any initial values for `branch`.
         */
        constructor(h: nat, l : seq<int>, f1 : (int, int) -> int, default : int) 
            requires h >= 1
            requires |l| == h 
            ensures Valid()
        {
            //  State variables
            TREE_HEIGHT, count, f, d := h, 0, f1, default;
            zero_h, branch := zeroes(f1, default, h - 1), l ;

            //  Ghost variables
            values := [];
            
            //  Proof that right siblings of path natToBitList2(0, h) are zero_h.
            bitToNatToBitsIsIdentity(0, h);
            valueIsZeroImpliesAllZeroes(natToBitList2(0, h));
            leafAtPathIsIntValueOfPath(natToBitList2(0, h), buildMerkle([], h, f1, default), 0, 0);
            rightSiblingsOfLastPathAreDefault(natToBitList2(0, h), buildMerkle([], h, f1, default), 0, f1, 0, default);
        }

        ///////////////////////////////////////////////////////////////////////////
        //  Functional versions of algorithms.
        ///////////////////////////////////////////////////////////////////////////

        /**
         *  The (almost) functional version deposit() function.
         *
         *  This method updates the left siblings (branch) in order
         *  to maintain the correspondence with the Merkle tree for values.
         *  This is captured by the Valid() predicate.
         *  In this version we use the functions operating on sequences
         *  in a functional style.
         *  
         *  @param  v   The new deposit amount.
         */
        method deposit_f(v : int) 
            requires Valid()
            requires count < power2(TREE_HEIGHT) - 1         
            ensures Valid()
            modifies this 
        {
            branch := computeLeftSiblingsOnNextpathWithIndex(TREE_HEIGHT, count, branch, zero_h, f, v);
            count := count + 1;

             //  Update ghost vars and prove correctness with new tree
            computeNewLeftIsCorrect(values, v, TREE_HEIGHT, old(branch), zero_h, f, d);
            values := values + [v];
        }   

        /**
         *  The get_deposit_root() functional function.
         *
         *  This method should always return the root value of the tree.
         *
         *  @returns    The root value of the Merkle Tree for values.
         */
        method {:timeMultiplier 2} get_deposit_root_f() returns (r : int) 
            requires Valid()
            ensures Valid()
            /** The result of get_deposit_root_() is the root value of the Merkle tree for values.  */
            ensures r == buildMerkle(values, TREE_HEIGHT, f, d).v 
            modifies {}
        {
            r := computeRootLeftRightUpWithIndex(TREE_HEIGHT, count, branch, zero_h, f, d);

            calc ==> {
                Valid();
                |values| < power2(TREE_HEIGHT);
            }
            assert |values| < power2(TREE_HEIGHT) ;

            //  The proof of post condition follows easily from:
            computeRootIsCorrect(values, TREE_HEIGHT, branch, zero_h, f, d);
        }

        ///////////////////////////////////////////////////////////////////////////
        //  Imperative versions of algorithms.
        ///////////////////////////////////////////////////////////////////////////

        /** 
         *  This method updates the left siblings (branch) in order
         *  to maintain the correspondence with the Merkle tree for values.
         *  This is captured by the Valid() predicate.
         *  
         *  @param  v   The new deposit amount.
         */
         method {:timeLimitMultiplier 5} deposit(v : int) 
            requires Valid()
            requires count < power2(TREE_HEIGHT) - 1         
            ensures Valid()
            modifies this 
        {
            var value := v;
            var size : nat := count;
            var i : nat := 0;
            
            ghost var e := computeLeftSiblingsOnNextpathWithIndex(TREE_HEIGHT, size, branch, zero_h, f, v);
            ghost var p := natToBitList(|values|, TREE_HEIGHT);

            //  Helpers for proving main invariant on entry
            calc == {
                branch;
                calc {
                    |branch| == TREE_HEIGHT;
                }
                take(branch, TREE_HEIGHT);
            }

            //  In our version branch and zero_h store the vectors in reverse order, so we
            //  use TREE_HEIGHT - i - 1  instead of index i < TREE_HEIGHT in the original algorith.
            //  @todo   Add a copy of branch in reverse order to use index i.
            //  Note that the test i < TREE_HEIGHT in the original
            //  version of the algorithm always evaluates to true and is redundant.
            while size % 2 == 1 
                modifies {}

                invariant branch == old(branch) 
                invariant values == old(values)
                invariant count == old(count)
                //  invariants related to range of index TREE_HEIGHT - i - 1 
                invariant 0 <= TREE_HEIGHT - i - 1 
                invariant 0 <= size < power2(TREE_HEIGHT - i) - 1
                
                invariant |branch| == |e| == |zero_h| == TREE_HEIGHT

                //  Main invariant:
                invariant e == 
                    computeLeftSiblingsOnNextpathWithIndex(
                        TREE_HEIGHT - i, size, 
                        take(branch, TREE_HEIGHT - i), 
                        take(zero_h, TREE_HEIGHT - i), f, value) 
                    + drop(branch, TREE_HEIGHT - i)     //  proving the + may need sone help

                //  Termination is easy as size decreases and must be zero.
                decreases size 
            {
                //  program loc at entry
                label E:

                mainInvariantProofHelper(TREE_HEIGHT - i, size, branch, zero_h, f, value);

                value := f(branch[TREE_HEIGHT - i - 1], value);
                size := size / 2;
                i := i + 1;

                assert(count == old@E(count));
                assert(branch == old@E(branch));
                assert(count == old@E(count));
            }

            assert(branch == old(branch));
            assert(count == old(count));
            assert(values == old(values));
            calc == {
                e;
                computeLeftSiblingsOnNextpathWithIndex(
                        TREE_HEIGHT - i, size, 
                        take(branch, TREE_HEIGHT - i), 
                        take(zero_h, TREE_HEIGHT - i), f, value) 
                    + drop(branch, TREE_HEIGHT - i);
                calc == {
                    computeLeftSiblingsOnNextpathWithIndex(
                        TREE_HEIGHT - i, size, 
                        take(branch, TREE_HEIGHT - i), 
                        take(zero_h, TREE_HEIGHT - i), f, value) ;
                    { assert(size % 2 == 0 && TREE_HEIGHT - i > 0 ); }
                    init(take(branch, TREE_HEIGHT - i)) + [value];
                }
                init(take(branch, TREE_HEIGHT - i)) + [value] + drop(branch, TREE_HEIGHT - i);
                { updateAndsplitSeqAtIndex(branch, value, TREE_HEIGHT - i);} 
                branch[TREE_HEIGHT - i - 1 := value];
                calc == {
                    branch;
                    old(branch);
                }
                old(branch)[TREE_HEIGHT - i - 1 := value];
            }
            //  This is the important hidden property: TREE_HEIGHT - i - 1 ( i < TREE_HEIGHT)
            //  in original version) is NEVER out of range, and always in [0, TREE_HEIGHT[
            branch := branch[TREE_HEIGHT - i - 1 := value];
            //  Correctness is: value of updated branch is the same as e.
            assert(branch == old(branch)[TREE_HEIGHT - i - 1 := value]);
            assert(branch == e);

            //  Finally increment count. Note that count can be incremented at the beginning
            //  provided that the while loop condition is flipped to size % 2 == 0.
            assert(count == old(count));
            count := count + 1;
            assert(count == old(count) + 1);

            values := values + [v];
            //  Constraints on height and length of lists.
            calc {
                |branch|;
                |old(branch)|;
                |e|;
                TREE_HEIGHT;
            }
            assert(1 <= TREE_HEIGHT == |branch| == |zero_h|);
            assert(count < power2(TREE_HEIGHT));
            //  count is the number of values added so far and should correspond to |values|.
            assert(|values| == count);
            //  zero_h is constant and equal to default values for each level of t.
            assert(zero_h == zeroes(f, d, TREE_HEIGHT - 1));
            //  branch and zero_h are the left and right siblings of path to 
            //  |values|-th leaf in buildMerkle(values, TREE_HEIGHT, f, d)
            computeNewLeftIsCorrect(old(values), v, TREE_HEIGHT, old(branch), zero_h, f, d);
            assert(values == old(values) + [v]);
            assert(areSiblingsAtIndex(|values|, buildMerkle(values, TREE_HEIGHT, f, d), branch, zero_h));
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
            requires 0 < k < power2(h) 
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
         */
         method get_deposit_root() returns (r : int) 
            requires Valid()
            ensures Valid()
            /** The result of get_deposit_root_() is the root value of the Merkle tree for values.  */
            ensures r == buildMerkle(values, TREE_HEIGHT, f, d).v 
            modifies {}
        {
            //  Some help to prove that the main invariant holds on entry:
            assert(take(branch, TREE_HEIGHT) == branch);
            assert(take(zero_h, TREE_HEIGHT) == zero_h);

            //  Store the expected result in a ghost variable.
            ghost var e := computeRootLeftRightUpWithIndex(TREE_HEIGHT, count, branch, zero_h, f, d);

            //  Start with default value for r.
            r := d;
            var h := 0;
            var size := count;

            while h < TREE_HEIGHT
                invariant branch == old(branch)
                invariant values == old(values)
                invariant count == old(count)

                //  no out of range in seqs:
                invariant 0 <= h <= TREE_HEIGHT
                invariant 0 <= size < power2(TREE_HEIGHT - h)
                //  Main invariant:
                invariant e == 
                    computeRootLeftRightUpWithIndex(
                        TREE_HEIGHT - h, size, 
                        take(branch, TREE_HEIGHT - h), take(zero_h, TREE_HEIGHT - h), f, r)

                decreases TREE_HEIGHT - h 
            {
                //  A little help for Dafny to check the proof:
                assert(last(take(branch, TREE_HEIGHT - h)) == branch[TREE_HEIGHT - h - 1]);
                assert(last(take(zero_h, TREE_HEIGHT - h)) == zero_h[TREE_HEIGHT - h - 1]);
                assert(init(take(branch, TREE_HEIGHT - h)) == take(branch, TREE_HEIGHT - h - 1));
                assert(init(take(zero_h, TREE_HEIGHT - h)) == take(zero_h, TREE_HEIGHT - h - 1));

                if size % 2 == 1 {
                    r := f(branch[TREE_HEIGHT - h - 1], r);
                } else {
                    r := f(r, zero_h[TREE_HEIGHT - h - 1]);
                }
                size := size / 2;
                h := h + 1;
                assert(
                    e == 
                    computeRootLeftRightUpWithIndex(
                        TREE_HEIGHT - h, size, 
                        take(branch, TREE_HEIGHT - h), take(zero_h, TREE_HEIGHT - h), f, r)
                );
            }

            //  By invariant at the end of the loop and definition of computeRootLeftRightUpWithIndex
            assert(e == computeRootLeftRightUpWithIndex(0, 0, [], [], f, r) == r);
            assert(1 <= TREE_HEIGHT);
            calc ==> {
                Valid();
                |values| < power2(TREE_HEIGHT);
            }
            assert |values| < power2(TREE_HEIGHT) ;
            assert |branch| == |zero_h| == TREE_HEIGHT ;
            assert areSiblingsAtIndex(|values|, buildMerkle(values, TREE_HEIGHT, f, d), branch, zero_h);

            //  The proof of post condition follows easily from:
            computeRootIsCorrect(values, TREE_HEIGHT, branch, zero_h, f, d);
        }
    }
}