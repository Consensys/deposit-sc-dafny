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

include "./synthattribute/ComputeRootPath.dfy"
include "./synthattribute/RightSiblings.dfy"
include "./helpers/Helpers.dfy"
include "./helpers/SeqHelpers.dfy"
include "./paths/PathInCompleteTrees.dfy"
include "./paths/NextPathInCompleteTreesLemmas.dfy"
include "./seqofbits/SeqOfBits.dfy"
include "./trees/Trees.dfy"
include "./MerkleTrees.dfy"
include "./intdiffalgo/IndexBasedAlgorithm.dfy"

/**
 *  A proof of correctness for the Deposit Smart Contract Algorithm, 
 *  This version usues while loops instead of the FP style version..
 */
module S {

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
    class D {

        //  State Variables.

        /** The default value for the leaves. */
        const d : int 

        /** The attribute function to synthesise. */
        const f : (int, int) -> int
    
        /** The height of the tree. */
        const TREE_HEIGHT : nat

        /** The values on the left siblings of the path to leaf of index k. */
        var branch : seq<int>

        /** The value sof the right siblings of path to leaf at index k. */
        const zero_h : seq<int>

        /** The number of values added to the list. Also the index of the next available leaf. */
        var count : nat 

        //  Ghost variables used for the correctness proof.

        /** The list of values added so far. */
        ghost var values : seq<int> 

        /** The (Merkle) tree that corresponds to the list of values added so far. */
        ghost var t : Tree<int>

        /** Path to index of next available leaf at index |values|. */
        ghost var p : seq<bit>

        /** Property to maintain to ensure correctness. */
        predicate Valid()
            reads this
        {
            //  Height and sequences sizes.
            1 <= TREE_HEIGHT ==  height(t) == |branch| == |zero_h| == |p|
            //  Maximum number of values stored in the tree bounded.
            && count < power2(TREE_HEIGHT) == |leavesIn(t)|
            //  count is the number of values added so far.
            && |values| == count
            //  t is the Merkle tree for values. 
            && isMerkle(t, values, f, d) && hasLeavesIndexedFrom(t, 0)
            //  zero_h is constant and equal to default values for each level of t.
            && zero_h == zeroes(f, d, TREE_HEIGHT - 1)
            //  Left and right siblings of `p` are given by branch and zero_h.
            //  p[i] == b means the sibling is at 1 - b, i.e. if p[i] == 0 (resp. 1), 
            //  sibling is at level i is the right (resp. left) child. 
            && (forall i :: 0 <= i < |p| ==> 
                siblingValueAt(p, t, i + 1) == 
                    if p[i] == 0 then zero_h[i] else branch[i]
            )
            //  `p` is the path to the next available slot in the tree at index `count`.
            && p == natToBitList(count, TREE_HEIGHT)
        }

        /**
         *  Initialisation.
         */
        constructor(h: nat, l : seq<int>, f1 : (int, int) -> int, default : int) 
            requires h >= 1
            requires |l| == h && forall i :: 0 <= i < |l| ==> l[i] == 0
            ensures Valid()
        {
            //  State variables
            TREE_HEIGHT, count, f, d := h, 0, f1, default;
            branch, zero_h := l, zeroes(f1, default, h - 1);

            //  Ghost variables
            t, values, p := buildMerkle([], h, f1, default), [],  natToBitList(0, h);
            
            //  Proof that right siblings of p are zero_h.
            bitToNatToBitsIsIdentity(0, h);
            valueIsZeroImpliesAllZeroes(natToBitList2(0, h));
            leafAtPathIsIntValueOfPath(natToBitList2(0, h), buildMerkle([], h, f1, default), 0, 0);
            rightSiblingsOfLastPathAreDefault(natToBitList2(0, h), buildMerkle([], h, f1, default), 0, f1, 0, default);
        }

        /** 
         *  This method updates the left siblings (branch) in order
         *  to maintain the correspondence with the Merkle tree for values.
         *  This is captured by the Valid() predicate.
         *  In this version we use the functions operating on sequences
         *  in a functional style.
         *  
         *  @param  v   The new deposit amount.
         */
        method deposit(v : int) 
            requires Valid()
            requires count < power2(TREE_HEIGHT) - 1         
            ensures Valid()
            modifies this 
        {
            ghost var nextTree :=  buildMerkle(values + [v], TREE_HEIGHT, f, d);
            assert(p == natToBitList(|values|, TREE_HEIGHT));

            //  Siblings of p in t are same as siblings on p in old(t)
            forall (i : nat | 0 <= i < |p|)
                ensures siblingValueAt(p, nextTree, i + 1) == 
                     siblingValueAt(p, old(t), i + 1) ==
                        if p[i] == 0 then
                             zero_h[i]
                        else 
                            branch[i]
            {
                reveal_siblingValueAt();
                nextPathSameSiblingsInNextList(
                    TREE_HEIGHT, values, v, old(t), 
                    nextTree, 
                    f, d, p);
            }
            
            bitToNatToBitsIsIdentity(count, TREE_HEIGHT);
            pathToNoLasthasZero(p);
            assert(exists i :: 0 <= i < |p| && p[i] == 0);

            forall ( i : nat | 0 <= i < |nextPath(p)| && nextPath(p)[i] == 1)
                ensures computeLeftSiblingOnNextPathFromLeftRight(p, branch, zero_h, f, v)[i]
                    ==
                    siblingValueAt(nextPath(p), nextTree, i + 1) 
            {
                computeLeftSiblingOnNextPathFromLeftRightIsCorrectInAMerkleTree(
                    p, values, v, nextTree, branch, zero_h, f, d
                );
            }

            pathToSucc(old(p), old(count), TREE_HEIGHT);
            assert(nextPath(p) == natToBitList(old(count) + 1, TREE_HEIGHT));

            var value := v;
            var size : nat := count;
            var i : nat := 0;
            
            ghost var e := computeLeftSiblingsOnNextpathWithIndex(TREE_HEIGHT, size, branch, zero_h, f, v);
            assert(branch == take(branch, TREE_HEIGHT - i));
            assert(zero_h == take(zero_h, TREE_HEIGHT - i));
            assert(|e| == TREE_HEIGHT);
            
            ///////////////////////////////////////////////////////////////////
            //  Compute new branch and increment count.
            //  This is the actual algorithm.
            ///////////////////////////////////////////////////////////////////

            while size % 2 == 1 
                invariant zero_h == old(zero_h) && t == old(t) && p == old(p) && count == old(count) && values == old(values)
                invariant 0 <= TREE_HEIGHT - i - 1 
                //  The next one is the important invariant that ensures
                //  that the update of branch after the loop does not
                //  result in a out of bounds error.
                invariant TREE_HEIGHT - i - 1 < TREE_HEIGHT == |branch| == |e| == |zero_h|
                //  The sequel are helper invariants
                invariant 0 <= size < power2(TREE_HEIGHT - i) - 1
                invariant TREE_HEIGHT - i <= |p|
                invariant size < power2(|take(p, TREE_HEIGHT - i)|)

                // invariant 
                invariant take(p, TREE_HEIGHT - i) == natToBitList2(size, TREE_HEIGHT - i)  // I1

                invariant e == 
                    computeLeftSiblingsOnNextpathWithIndex(
                        TREE_HEIGHT - i, size, 
                        take(branch, TREE_HEIGHT - i), 
                        take(zero_h, TREE_HEIGHT - i), f, value) 
                    + drop(branch, TREE_HEIGHT - i);

                //  Termination is easy as size decreases and must be zero.
                decreases size 
            {
                //  Some help to verify I1:
                div2IsInit(size, take(p, TREE_HEIGHT - i));
                assert(init(take(p, TREE_HEIGHT - i)) == take(p, TREE_HEIGHT - i - 1));

                //  Some help to verify I2:
                assert(init(take(branch, TREE_HEIGHT - i)) == take(branch, TREE_HEIGHT - i - 1));
                assert(init(take(zero_h, TREE_HEIGHT - i)) == take(zero_h, TREE_HEIGHT - i - 1));
                assert(last(take(branch, TREE_HEIGHT - i)) == branch[TREE_HEIGHT - i - 1]);

                value := f(branch[TREE_HEIGHT - i - 1], value);
                size := size / 2;
                i := i + 1;
            }
            assert(count == old(count));
            assert(e == computeLeftSiblingsOnNextpathWithIndex(
                        TREE_HEIGHT - i, size, 
                        take(branch, TREE_HEIGHT - i), 
                        take(zero_h, TREE_HEIGHT - i), f, value) 
                    + drop(branch, TREE_HEIGHT - i));
            assert(size % 2 == 0);
            assert( e == init(take(branch, TREE_HEIGHT - i)) + [value] + drop(branch, TREE_HEIGHT - i));
            //  This is the important hidden property: TREE_HEIGHT - i - 1 is NEVER 
            //  out of range. 
            branch := branch[TREE_HEIGHT - i - 1 := value];
            assert(count == old(count));
            // assert(branch == e);

            assert(zero_h == old(zero_h));
            assert(t == old(t));
            assert(count == old(count));
            count := count + 1;

            //  Update ghost vars
            values := values + [v];
            p := nextPath(p);
            t := buildMerkle(values, TREE_HEIGHT, f, d);
            
            pathToLastInMerkleTreeHasZeroRightSiblings(p, values, t, f, d);
            assert(
                forall i :: 0 <= i < |p| && p[i] == 0 ==> 
                    siblingValueAt(p, t, i + 1) == zero_h[i]
            );
            assert(
                forall i :: 0 <= i < |p| && p[i] == 1 ==> 
                    siblingValueAt(p, t, i + 1) == branch[i]
            );
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
            /** The result of get_deposit_root_() is the root value of the tree.  */
            ensures r == t.v
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
            }

            //  The correstness proof:
            //  By invariant at the end of the loop and definition of computeRootLeftRightUpWithIndex
            assert(e == computeRootLeftRightUpWithIndex(0, 0, [], [], f, r) == r);
            //  The proof of post condition follows easily from the correctness
            //  of computeRootLeftRightUpWithIndex
            computeRootUsingDefaultIsCorrectInAMerkleTree(p, values, t, branch, zero_h, f, d);
        }
    }
}