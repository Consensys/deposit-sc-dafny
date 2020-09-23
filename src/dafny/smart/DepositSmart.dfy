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

        /** The number of values added to the tree. */
        // ghost var count : nat 

        /** The (Merkle) tree that corresponds to the list of values added so far. */
        ghost var t : Tree<T>

        /** The value of the root of the tree. */
        // ghost var r : T

        /** The list of values added so far. */
        ghost var values : seq<T> 

        /** Path to index of next available leaf. */
        ghost var p : seq<bit>

        /** The values on the left siblings on p. */
        // ghost var left : seq<T>

        /** Property to maintain. */
        predicate Valid()
            reads this
        {
            //  Height and sequences sizes
            1 <= TREE_HEIGHT ==  height(t) == |branch| == |zero_h| == |p|
            //  tree is not full
            && count < power2(TREE_HEIGHT)

            && |values| == count <= power2(TREE_HEIGHT) == |leavesIn(t)|

            //  t is the Merkle tree for the valuea added so far. 
            && isMerkle(t, values, f, d) && hasLeavesIndexedFrom(t, 0)

            && zero_h == zeroes(f, d, TREE_HEIGHT - 1)
            && (forall i :: 0 <= i < |zero_h| ==> 
                    zero_h[i] == defaultValue(f, d, height(t) - 1 - i)
            )
            //  The right siblings of the current path are all zeroes
            && (forall i :: 0 <= i < |p| ==> 
                    siblingValueAt(p, t, i + 1) == 
                        if p[i] == 0 then
                             zero_h[i]
                        else 
                            branch[i]
            )

            // && (r == t.v)
            //  Path is to current next free leaf.
            // && bitListToNat(p) == count
            && p == natToBitList(count, TREE_HEIGHT)
            // && nodeAt(p, t) == leavesIn(t)[count]
            // && nodeAt(p, t).v == lastVal

            //  Branch has values of left siblings of current path
            // && (forall i :: 0 <= i < |branch| && p[i] == 1 ==> 
            //         siblingValueAt(p, t, i + 1) == branch[i])

            // && (forall i :: 0 <= i < |left| && p[i] == 1 ==> 
            //         siblingValueAt(p, t, i + 1) == left[i])
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
            // left := l;
            //  Path to the first available leaf at index 0.
            p := natToBitList2(0, h);
            bitToNatToBitsIsIdentity(0, h);
            valueIsZeroImpliesAllZeroes(natToBitList2(0, h));
            leafAtPathIsIntValueOfPath(natToBitList2(0, h), buildMerkle([], h, fun, default), 0, 0);

            rightSiblingsOfLastPathAreDefault(natToBitList2(0, h), buildMerkle([], h, fun, default), 0, fun, 0, default);
            //  Initially r is value of f for all leaves equal to default.
            // r := defaultValue(fun, default, h);
            //  Use lemma to prove that r == t.v
            allLeavesDefaultImplyRootNodeDefault(buildMerkle([], h, fun, default), fun, default);
        }

        
        method dep(v : T) 
            requires Valid()
            requires count < power2(TREE_HEIGHT) - 1         

            ensures 1 <= TREE_HEIGHT ==  height(t) == |branch| == |zero_h| == |p|
            ensures values == old(values) + [v]
            ensures 1 <= |values| <= power2(height(t))
            ensures count == old(count) + 1
            ensures exists i :: 0 <= i < |old(p)| && old(p)[i] == 0
            ensures p == nextPath(old(p))

            ensures isMerkle(t, values, f, d) && hasLeavesIndexedFrom(t, 0)
            ensures p == natToBitList(count, TREE_HEIGHT)
            ensures count < power2(TREE_HEIGHT)
            ensures |values| == count <= power2(TREE_HEIGHT) == |leavesIn(t)|

            ensures zero_h == zeroes(f, d, TREE_HEIGHT - 1)
            ensures (forall i :: 0 <= i < |p| ==> 
                    siblingValueAt(p, t, i + 1) == 
                        if p[i] == 0 then
                             zero_h[i]
                        else 
                            branch[i])
           
            // ensures Valid()

            modifies this 
        {
            t := buildMerkle(values + [v], TREE_HEIGHT, f, d);

            nextPathSameSiblingsInNextList(TREE_HEIGHT, values, v, old(t), t, f, d, p);
            assert(
                reveal_siblingValueAt();
                forall i :: 0 <= i < |p|  ==>
                    siblingValueAt(p, t, i + 1) == siblingValueAt(p, old(t), i + 1)
            );

            assert(
                reveal_siblingValueAt();
                forall i :: 0 <= i < |p| ==> 
                    siblingValueAt(p, t, i + 1) == 
                    siblingValueAt(p, old(t), i + 1) == 
                        if p[i] == 0 then
                             zero_h[i]
                        else 
                            branch[i]
            );

            values := values + [v];

            bitToNatToBitsIsIdentity(count, TREE_HEIGHT);
            leafAtPathIsIntValueOfPath(p, t, count, 0);
            
            computeLeftSiblingOnNextPathFromLeftRightIsCorrectInATree(p, t, branch, zero_h, f, v, count);

            assert(
                forall i :: 0 <= i < |p| && nextPath(p)[i] == 1 ==> 
                computeLeftSiblingOnNextPathFromLeftRight(p, branch, zero_h, f, v)[i] == siblingAt(take(nextPath(p), i + 1),t ).v
            );

            branch := computeLeftSiblingsOnNextpathWithIndex(TREE_HEIGHT, count, branch, zero_h, f, v);

            bitToNatToBitsIsIdentity(count, TREE_HEIGHT);
            pathToNoLasthasZero(p);
            assert(exists i :: 0 <= i < |p| && p[i] == 0);

            p := nextPath(p);

            assert(count == old(count));
            count := count + 1;
            assert count == old(count) + 1;

            pathToSucc(old(p), old(count), TREE_HEIGHT);

            assert(
                forall i :: 0 <= i < |p| && p[i] == 1 ==> 
                    branch[i] == siblingAt(take(p, i + 1),t ).v
            );

            
            assume(p == natToBitList(|values| - 1, TREE_HEIGHT));
            assume(height(t) == TREE_HEIGHT);

            // pathToLastInMerkleTreeHasZeroRightSiblings(p, values, t, f, d);
            // assert(
            //     // reveal_siblingValueAt();
            //     forall i :: 0 <= i < |p| && p[i] == 0 ==> 
            //         // siblingValueAt(p, t, i + 1) 
            //         // siblingAt(take(p, i + 1),t ).v ==
            //         zeroes(f, d, height(t) - 1)[i] 
            //         == zero_h[i]
            // );
            forall ( i : nat | 0 <= i < |p| && p[i] == 0) 
                // ensures siblingAt(take(p, i + 1),t ).v 
                ensures siblingValueAt(p, t, i + 1) ==  zeroes(f, d, height(t) - 1)[i] 
                // == zero_h[i]
            {
                //  reveal_siblingValueAt();
                pathToLastInMerkleTreeHasZeroRightSiblings(p, values, t, f, d);
            }
        }
        
        /**
         *  Deposit a value i.e update the state.
         */
        // method deposit(v : T) 
        //     requires Valid()
        //     requires count < power2(TREE_HEIGHT) - 1 
            
        //     ensures 1 <= TREE_HEIGHT ==  height(t) == |branch| == |zero_h| == |left| == |p|
        //     ensures count < power2(TREE_HEIGHT) 
        //     ensures |values| == count < power2(TREE_HEIGHT) == |leavesIn(t)|
        //     ensures isMerkle(t, values, f, d)

        //     ensures p == natToBitList(old(count) + 1, TREE_HEIGHT)
        //     ensures count == old(count) + 1
        //     ensures p == natToBitList(count, TREE_HEIGHT)

        //     // ensures (forall i :: 0 <= i < |p| && p[i] == 1 ==> 
        //     //         siblingValueAt(p, t, i + 1) == branch[i]
                        
        //     // ensures nodeAt(p, t) == leavesIn(t)[count]

        //     //  left siblings post condition


        //     modifies this 
        // {
        //     t := buildMerkle(values + [v], TREE_HEIGHT, f, d);
        //     assert(hasLeavesIndexedFrom(t, 0));
        //     assert(isCompleteTree(t));
        //     bitToNatToBitsIsIdentity(old(count), TREE_HEIGHT) ;
        //     bitToNatToBitsIsIdentity(count, TREE_HEIGHT) ;
        //     assert( bitListToNat(old(p)) == old(count));
        //     assert( bitListToNat(p) == count);
        //     leafAtPathIsIntValueOfPath(p, t, count, 0);
        //     leafAtPathIsIntValueOfPath(old(p), t, old(count), 0);
        //     assert(nodeAt(old(p), t) == leavesIn(t)[old(count)]);
        //     assert(nodeAt(p, t) == leavesIn(t)[count]);


        //     nextPathSameSiblingsInNextList(TREE_HEIGHT, values, v, old(t), t, f, d, p);
        //     assert(
        //         reveal_siblingValueAt();
        //         forall i :: 0 <= i < |p|  ==>
        //             siblingValueAt(p, t, i + 1) == siblingValueAt(p, old(t), i + 1)
        //     );

        //     computeLeftSiblingOnNextPathFromLeftRightIsCorrectInATree(old(p), t, branch, zero_h, f, v, old(count));

        //     // computeLeftSiblingOnNextPathFromLeftRightIsCorrectInATree(p, t, branch, zero_h, f, v, count);

        //     // assert(
        //     //     forall i :: 0 <= i < |old(p)| && nextPath(old(p))[i] == 1 ==> 
        //     //     computeLeftSiblingOnNextPathFromLeftRight(old(p), branch, zero_h, f, v)[i] == siblingAt(take(nextPath(old(p)), i + 1),t ).v
        //     // );

        //     //  prove properties on left siblings.

        //     values := values + [v];

        //     //  before computing nextPath(p), prove bitListToNat(p) < power2(|p|) - 1
        //     bitToNatToBitsIsIdentity(old(count), TREE_HEIGHT) ;
        //     pathToNoLasthasZero(old(p));
        //     assert(bitListToNat(old(p)) < power2(|old(p)|) - 1);
            
        //     p :=  nextPath(p);
            
        //     ghost var x := computeLeftSiblingsOnNextpathWithIndex(TREE_HEIGHT, count, old(branch), zero_h, f, v);
        //     //  Compute left siblings on next path to (count + 1)-th leaf. 
        //     branch := computeLeftSiblingsOnNextpathWithIndex(TREE_HEIGHT, count, branch, zero_h, f, v);
        //     assert(branch == x
        //         // computeLeftSiblingsOnNextpathWithIndex(TREE_HEIGHT, count, old(branch), zero_h, f, v)
        //         == computeLeftSiblingOnNextPathFromLeftRight(natToBitList(count, TREE_HEIGHT), old(branch), zero_h, f, v)
        //     );
        //     //
            

        //     count := count + 1;
        //     assert(count == old(count) + 1);
        //     assert(old(count) < power2(TREE_HEIGHT) - 1);
        //     assert(count ==  old(count) + 1 < power2(TREE_HEIGHT) - 1 + 1);
        //     assert(p ==  nextPath(old(p)));
        //     pathToSucc(old(p), old(count), TREE_HEIGHT);
        //     assert(p == natToBitList(count, TREE_HEIGHT));
            
        //     //  branch is left siblings on path to count
        //     // assert();
        //     // assert (forall i :: 0 <= i < |p| && p[i] == 1 ==> 
        //     //         siblingValueAt(p, t, i + 1) == branch[i]);
        // }


        method get_deposit_root() returns (h_root: T) 
            requires Valid()
            requires count < power2(TREE_HEIGHT) - 1 

            // ensures count == 0 ==> h_root == t.v 
        {
            //  Show that d == nodeAt(p, t).v
            // calc == {
            //     nodeAt(p, t).v;
            //     leavesIn(t)[natToBitList2(count, h)].v;

            // }
            // assume(d == nodeAt(p, t).v);
            // assert(bitListToNat(p) == count);
            // bitToNatToBitsIsIdentity(count, TREE_HEIGHT);
            // assert(p == natToBitList(count, TREE_HEIGHT));

            // reveal_siblingValueAt();
            // computeRootLeftRightUpIsCorrectForTree(p, t, branch, zero_h, f, d);
 
            //  Compute the root using the left siblings on next path (branch) and default value d.
            h_root := computeRootLeftRightUpWithIndex(TREE_HEIGHT, count, branch, zero_h, f, d);
            // assert(
            //     computeRootLeftRightUpWithIndex(TREE_HEIGHT, count, branch, zero_h, f, d)
            //     ==
            //     computeRootLeftRightUp(natToBitList2(count, TREE_HEIGHT), branch, zero_h, f, d)
            //     ==
            //     computeRootLeftRightUp(p, branch, zero_h, f, d)

            // );
            // assert(t.v == computeRootLeftRightUp(p, branch, zero_h, f, d));
        }

        

        /**
         *  Deposit a value i.e update the state.
         */
        // method deposit2(value : T) 
        //     requires Valid()
        //     requires count < power2(TREE_HEIGHT) - 1 

        //     modifies this 
        // {
            //  Update ghost variables that simulate what is happening on the Merkle tree.
            //  Add value to tree 
            // values := values + [value];
            // assert(|values| == count + 1 < power2(TREE_HEIGHT));
            // t := buildMerkle(values, TREE_HEIGHT, f, d);
            // assert(height(t) == TREE_HEIGHT);
            // assert(isMerkle(t, values, f, d));

            // nextPathSameSiblingsInNextList(TREE_HEIGHT, old(values), value, old(t), t, f, d, p, nextPath(p));
            // r := computeRootLeftRightUpWithIndex(TREE_HEIGHT, count + 1, branch, zero_h, f, value);
            // computeWithIndexFromZeroIsCorrect(TREE_HEIGHT, count, branch, zero_h, f, value);
            // computeRootLeftRightIsCorrectForTree(natToBitList(count, TREE_HEIGHT), t, branch, zero_h, f, value);
            // assert(r == t.v);            

            // //  Compute nextPath
            // //  We have to show p (path to count-th leaf, has a zero
            // assert(bitListToNat(p) == count < power2(TREE_HEIGHT) - 1 == power2(|p|) - 1);
            // pathToNoLasthasZero(p);
            // p := nextPath(p);
            // //  p is path to (count + 1)-th leaf
            // nextPathIffSucc(old(p), p);
            // assert(bitListToNat(p) == bitListToNat(old(p)) + 1 == count + 1);
            // leafAtPathIsIntValueOfPath(p, t, count + 1 , 0);
            // assert(nodeAt(p, t) == leavesIn(t)[count + 1]);

            // computeLeftSiblingOnNextPathFromLeftRightIsCorrectInATree(natToBitList(count + 1, TREE_HEIGHT), t, branch, zero_h, f, value, count);

           
            //  Depsoit contract algorithm
            //  Compute left siblings on next path to (count + 1_th leaf. 
            // branch := computeLeftSiblingsOnNextpathWithIndex(TREE_HEIGHT, count, branch, zero_h, f, value);
            // count := count + 1;

            // assert();

            //  branch is the value of siblings on next path.
            // assert(branch == computeLeftSiblingOnNextPathFromLeftRight(natToBitList(count, TREE_HEIGHT), left, zero_h, f, value));
            
            // computeLeftSiblingOnNextPathFromLeftRight();
        // }

    }

}