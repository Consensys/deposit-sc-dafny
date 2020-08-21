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
include "Helpers.dfy"
include "Trees2.dfy"
include "IncAlgoV3.dfy"
include "MerkleTrees.dfy"
include "SeqOfBits.dfy"
include "CompleteTrees.dfy"
include "PathInCompleteTrees.dfy"
include "SeqHelpers.dfy"

module IntTreeIncAlgo { 

    import opened Helpers
    import opened DiffTree
    import opened IncAlgoV3
    import opened Trees
    import opened MerkleTrees
    import opened SeqOfBits
    import opened CompleteTrees
    import opened PathInCompleteTrees
    import opened SeqHelpers

    /**
     *  Incremental algorithm.
     *
     *  @todo   Add data structures and complete method add to
     *          correctly compute diffRoot. 
     */
    class IntTree {

        /**  The root tracking the Merkle Tree. */
        ghost var root : Tree<int>

        /** Height of the tree */
        var h : nat 

        /** diffRoot, the value of diff on the root. */
        var diffRoot : int

        /** Number of elements in the tree. */
        var counter : nat

        /** The list of ints stored in the tree.  */
        ghost var store : seq<int>

        var valLeft : seq<int>

        /** A valid tree. */
        predicate isValid() 
            requires isCompleteTree(root)
            reads this
        {
            //  Use lemmas relating number of leaves and height of a complete tree.
            completeTreeNumberLemmas(root);

            //  The tree is correctly decorated by diff.
            isDecoratedWithDiff(root)
            //  diffRoot is the value of diff on root.
            && diffRoot == root.v
            //  height preserved.
            && h == height(root) == |valLeft|
            && 0 <= |store| == counter <= power2(h - 1)
            && |leavesIn(root)| == power2(h - 1)

            //  tree leftmost leaves are in store.
            && treeLeftmostLeavesMatchList(store, root, 0)
        }

        /**
         *  Initial tree of height initH and all leaves set to 0.
         */
        constructor(initH: nat) 
            requires initH >= 1
            ensures height(root) == h == initH
            ensures treeLeftmostLeavesMatchList([], root, 0)
            ensures store == []
            ensures isCompleteTree(root)
            ensures isValid()

        /**
         *  The Merkle tree of height `h` for the empty list is the 
         *  zero (complete) tree of height `h`.
         */
        // lemma merkleEmptyListIsZeroTree(h : nat)
        //     requires h >= 1 
        //     ensures isZeroTree(buildMerkle([], h))
        // {
        //     allLeavesZeroImplyAllNodesZero(buildMerkle([], h));
        //     isZeroTreeiffAllNodesZero(buildMerkle([], h));
        // }   
       
       
        /**
         *  The leaf at index k < 2^(h - 1)/2 is in lc, and index >= 2^(h - 1)/2
         *  is in rc.
         *  @todo   Check whether this lemma is useful and not superseded by p3.
         */
        // lemma {:induction r} p1(r : Tree<int>, k : nat)
        //     requires isCompleteTree(r)
        //     requires height(r) >= 2
        //     requires 0 <= k < power2(height(r) - 1 ) 
        //     ensures match r 
        //         case Node(_, lc, rc )=> 
        //             ((0 <= k < power2(height(r) - 1 ) / 2) ==>
        //                 k < |leavesIn(lc)|
        //                 && leavesIn(r)[k] == leavesIn(lc)[k]
        //             )
        //             && 
        //                 (power2(height(r) - 1) / 2 <= k < power2(height(r) - 1) ==> 
        //                 && 0 <= k - power2(height(r) - 1)/2 < |leavesIn(rc)|
        //                 && k < |leavesIn(r)|
        //                 && leavesIn(r)[k] == leavesIn(rc)[k - power2(height(r) - 1)/2]
        //                 )
        // {
        //     completeTreesLeftRightHaveSameNumberOfLeaves(r);
        //     completeTreesLeftRightChildrenLeaves(r, height(r)) ;
        // }

        /**
         *  Values of the nodes on the right of a path to e in Merkle(l :+ e,h)
         *  are all zeroes.
         */
        // lemma nodesOnRightSiblingsZero(p: seq<bit>, r: Tree<int>, l: seq<int>, e : int, h: nat)
        //     requires h == height(r) >= 1
        //     /** */
        //     requires |l| + 1 <= |leavesIn(r)|
        //     requires isMerkle(r, l + [e], diff, 0)
        //     /** `p` is a path to `e`. */
        //     requires |p| == h - 1
        //     requires nodeAt(p, r).id == p 

        //     requires |l| + 1 <=  |leavesIn(r)| / 2
        //     ensures forall n :: 0 <= n < |p| ==> 
        //         p[n] == 0 ==> siblingAt(p, r).v == 0 
        // {
        //     if h == 1 {
        //         //  Thanks Dafny
        //     }
        //     else {
        //         // match r 
        //         //     case Node(_, lc, rc) =>
        //     }
        // }

        /**
         *  The value of diff at the root of a well decorated tree is the value of
         *  the tree.
         */
        // function hash_tree_root(r: Tree<int>) : int 
        //     requires isCompleteTree(r)
        //     requires isDecoratedWithDiff(r) 
        // {
        //     r.v
        // }

        /** 
         *  Add element e to the tree.
         *
         *  @param  e   The element to add to the store.
         *
         *  @todo       This algorithm should maintain the invariant
         *              `diffRoot == root.v`.
         */
        method add(e: int)

            requires isCompleteTree(root)
            requires h == height(root) 
            requires |store| < power2(h - 1)

            requires |leavesIn(root)| == power2(h - 1)
            requires isDecoratedWith(diff, root)
            requires treeLeftmostLeavesMatchList(store, root, 0)
            requires isMerkle(root, store, diff, 0)
            requires isValid()

            //  Store is updated
            ensures store == old(store) + [ e ]

            //  Preserves tree height and completeness
            ensures  old(h) == h
            //  Store is not full
            ensures isCompleteTree(root)

            ensures |leavesIn(root)| == power2(h - 1)

            //  diffRoot stores value of diff for store
            ensures isDecoratedWithDiff(root)
            ensures |store| <= power2(h - 1)
            ensures treeLeftmostLeavesMatchList(store, root, 0)

            //  The next one is not verified in the current version of this algo.
            ensures diffRoot == root.v

            // ensures isValid()

            modifies this
        {
            //  Update store
            store := store + [ e ] ;
            
            //  Define new tree for updated store
            root := buildMerkleDiff(store, h);

            //  Compute the new diffRoot
            diffRoot := computeRootPathDiffAndLeftSiblingsUpv4(h, counter, valLeft, e).0 ;
            diffRoot := 0 ;
        }

    } 
}
