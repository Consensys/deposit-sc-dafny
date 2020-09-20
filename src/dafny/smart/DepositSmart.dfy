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

include "./trees/CompleteTrees.dfy"
include "./synthattribute/ComputeRootPath.dfy"
include "./synthattribute/RightSiblings.dfy"
include "./synthattribute/Siblings.dfy"
include "./synthattribute/GenericComputation.dfy"
include "./helpers/Helpers.dfy"
include "./paths/PathInCompleteTrees.dfy"
include "./paths/NextPathInCompleteTreesLemmas.dfy"
include "./seqofbits/SeqOfBits.dfy"
include "./helpers/SeqHelpers.dfy"
include "./trees/Trees.dfy"
include "./MerkleTrees.dfy"

include "./intdiffalgo/IndexBasedAlgorithm.dfy"

module DepositSmart {

    import opened CompleteTrees
    import opened ComputeRootPath
    import opened RSiblings
    import opened Siblings
    import opened Helpers
    import opened NextPathInCompleteTreesLemmas
    import opened PathInCompleteTrees
    import opened SeqOfBits
    import opened SeqHelpers
    import opened Trees 
    import opened MerkleTrees
    import opened GenericComputation

    import opened IndexBasedAlgorithm
    
    /**
     *  The functional version of the deposit smart contract.
     */
    class Deposit<T> {

        //  State Variables.

        /** The default value for the leaves. */
        const d : T 

        /** The attribute function to synthesise. */
        const f : (T, T) -> T

        /** The height of the tree. */
        const TREE_HEIGHT : nat

        /** The values on the left siblings of the path to leaf of index k. */
        var branch : seq<T>

        /** The value sof the right siblings of path to leaf at index k. */
        const zero_h : seq<T>

        /** The number of values added to the list. Also the index of the next available leaf. */
        var count : nat 

        //  Ghost variables used for the correctness proof.

        /** The (Merkle) tree that corresponds to the list of values added so far. */
        ghost var t : Tree<T>

        /** The value of the root of the tree. */
        ghost var r : T

        /** The list of values added so far. */
        ghost var values : seq<T> 

        /** Path to current to the leaf of index count. */
        ghost var p : seq<bit>

        /** The values on the left siblings of current path. */
        ghost var left : seq<T>

        /** Property to maintain. */
        predicate Valid()
            reads this
        {
            //  Height and sequences sizes
            1 <= TREE_HEIGHT ==  height(t) == |branch| == |zero_h| == |left| == |p|
            //  tree is not full
            && count < power2(TREE_HEIGHT)

            && |values| <= power2(TREE_HEIGHT) == |leavesIn(t)|

            //  t is the Merkle tree for the valuea added so far. 
            && isMerkle(t, values, f, d)
            //  The right siblings of the current path are all zeroes
            && (forall i :: 0 <= i < |zero_h| && p[i] == 0 ==> 
                    siblingValueAt(p, t, i + 1) == zero_h[i])

            && (r == t.v)
            //  Path is to current next free leaf.
            && bitListToNat(p) == count

            //  Branch has values of left siblings of current path
            && (forall i :: 0 <= i < |branch| && p[i] == 1 ==> 
                    siblingValueAt(p, t, i + 1) == branch[i])

            && (forall i :: 0 <= i < |left| && p[i] == 1 ==> 
                    siblingValueAt(p, t, i + 1) == left[i])
        }

        /**
         *  Initialise the system, tree of size >= 1.
         */
        constructor(h: nat, l : seq<T>, default : T, fun : (T, T) -> T) 
            requires h >= 1
            requires |l| == h && forall i :: 0 <= i < |l| ==> l[i] == default
            ensures Valid()
        {
            //  State variables

            TREE_HEIGHT, count, d, f := h, 0, default, fun;
            branch, zero_h := l, zeroes(fun, default, h - 1);

            //  Ghost variables

            //  The initial tree is the Merkle tree for brancn (or l).
            t := buildMerkle([], h, fun, default);
            //  The values that have been added is initially empty.
            values := [];
            //  possibly left could be left uninitialised
            left := l;
            //  Path to the first available leaf at index 0.
            p := natToBitList2(0, h);
            bitToNatToBitsIsIdentity(0, h);
            valueIsZeroImpliesAllZeroes(natToBitList2(0, h));

            rightSiblingsOfLastPathAreDefault(natToBitList2(0, h), buildMerkle([], h, fun, default), 0, fun, 0, default);
            //  Initially r is value of f for all leaves equal to default.
            r := defaultValue(fun, default, h);
            //  Use lemma to prove that r == t.v
            allLeavesDefaultImplyRootNodeDefault(buildMerkle([], h, fun, default), fun, default);
        }

        method get_deposit_root() returns (h_root: T) 
            requires Valid();
            ensures h_root == t.v 
        {
            h_root := computeRootLeftRightUpWithIndex(TREE_HEIGHT, count, branch, zero_h, f, d);
        }
        /**
         *  Deposit a value i.e update the state.
         */
        // method deposit(value : T) 
        //     requires Valid()
        //     requires count < power2(TREE_HEIGHT) - 1

        //     requires (forall i :: 0 <= i < |zeroes| && p[i] == 1 ==> 
        //             siblingAt(take(p, i + 1), t).v == branch[i])

        //     ensures Valid()
            
        //     modifies this

        // {
        //     //   Update values
        //     values := values[count := value];
        //     //  Update tree
        //     t := buildMerkle(values, TREE_HEIGHT, f, d);
        //     //  The trees old(t) and t have same leaves except possibly at count
        //     assert(take(leavesIn(old(t)), count) == take(leavesIn(t), count));
        //     assert(drop(leavesIn(old(t)), count + 1) == drop(leavesIn(t), count + 1));
            
           

        //     bitToNatToBitsIsIdentity(count, TREE_HEIGHT);
        //     assert(bitListToNat(p) == count < power2(TREE_HEIGHT) - 1);

        //     //  the trees old(t) and t have same left siblings
        //     //  they have similar values upto count.
        // // requires drop(leavesIn(r), k + 1) == drop(leavesIn(r'), k + 1)
        // assert(isCompleteTree(t));
        // assert(isCompleteTree(old(t)));
        // assert(isDecoratedWith(f, t));
        // assert(isDecoratedWith(f, old(t)));
        // assert(height(t) == height(old(t)) >= 1);
        // assert(hasLeavesIndexedFrom(t, 0));
        // assert(hasLeavesIndexedFrom(old(t), 0));
        // assert(1 <= |p| <= height(t));
        // assert(count < |leavesIn(t)| == |leavesIn(old(t))| );
        // leftSiblingsInEquivTrees2(p, old(t), t, count, f, 0);

        // //  Show that value is nodeAt(p, t).v
        // leafAtPathIsIntValueOfPath(p, t, count, 0);
        // assert(nodeAt(p, t).v == leavesIn(t)[count].v == value);
        // //  This proves that t has same siblings as old(t) for path p.
        // computeRootLeftRightIsCorrectForTree(p, t, branch, zeroes, f, value);

        //   //  compute root value
        //     r := computeRootLeftRight(p, branch, zeroes, f, value);

        // assert(t.v == r);

        //     //   update path 
        //     //   as p is to non last leaf it must have a zero and nextPath 
        //     //   can be computed
            
        //     pathToNoLasthasZero(p);
        //     nextPathIsSucc(p);
        //     assert(bitListToNat(nextPath(p)) == bitListToNat(p) + 1 == count + 1);
        //     p := nextPath(p);
        //     count := count + 1;

        //     //  p is still the path to leaf at index count
        //     bitToNatToBitsIsIdentity(count, TREE_HEIGHT);
        //     assert(bitListToNat(p) == count);

        //     //  Prove that right siblings of new path are still zeroes
        //     rightSiblingsOfLastPathAreDefault(p, t, count, f, 0, d, zeroes);

        //     assert(t.v == r);

            
        // }

    }

}