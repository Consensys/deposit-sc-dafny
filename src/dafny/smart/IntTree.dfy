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

include "Helpers.dfy"
include "Trees.dfy"
include "MerkleTrees.dfy"

module DiffTree {

    import opened Helpers
    import opened Trees
    import opened MerkleTrees

    //  Trees holding integer values as attribute.
    type Intnode = Node<int>

    /** 
     *  Difference between two integers.
     *
     *  @note:  This could be inlined in the predicate
     *          isDecoratedWithDiff, but we may use another 
     *          function later, so we factor it out.
     */
    function diff(a: int, b : int) : int 
    {
        a - b
    }

    /**
     *  Check that a decorated tree correctly stores the diff attribute. 
     */
    predicate isDecoratedWithDiff(root: Node<int>)
        decreases root
    {
        match root
            case Leaf(v, _, _) => true

            case Node(v, lc, rc, _, _) => 
                v == diff(lc.v, rc.v)
                && isDecoratedWithDiff(lc)
                && isDecoratedWithDiff(rc)
    }

    /**
     *  Incremental algorithm.
     *
     *  @todo   Add data structures and complete method add to
     *          correctly compute diffRoot. 
     */
    class IntTree {

        /**  The root tracking the Merkle Tree. */
        ghost var root : Node<int>

        /** Height if the tree */
        var height : nat 

        /** diffRoot, the value of diff on the root. */
        var diffRoot : int

        /** Number of elements in the tree. */
        // var counter : nat

        ghost var store : seq<int>

        /** A valid configuration. */
        predicate isValid() 
            requires Trees.isCompleteTree(root)
            reads this
        {
            completeTreeNumberOfLeaves(root);

            //  tree correctly decorated by diff.
            isDecoratedWithDiff(root)
            //  diffRoot is the value of diff on root.
            && diffRoot == root.v
            //  height preserved.
            && height == Trees.height(root) 
            && 0 <= |store| <= power2(height - 1)
            && |collectLeaves(root)| == power2(height - 1)

            //  tree leftmost leaves are in store.
            && MerkleTrees.treeLeftmostLeavesMatchList(store, root, 0)
        }

        /**
         *  Initial tree of height h and all leaves set to 0.
         */
        constructor(h: nat) 
            requires h >= 1
            ensures Trees.height(root) == h == height
            ensures MerkleTrees.treeLeftmostLeavesMatchList([], root, 0)
            ensures store == []
            ensures Trees.isCompleteTree(root)
            ensures isValid()

        /** Defines the Int Tree for a given sequence.
         *  
         *  @note   This function does not compute the tree but rather
         *          defines its properties: correctly stores the attribute
         *          `diff` and the leftmost |l| leaves store l.
         */
        function buildMerkle(l: seq<int>, h : nat) : Node<int> 
            requires h >= 1
            requires |l| <= power2(h - 1)
            ensures Trees.height(buildMerkle(l, h)) == h
            ensures Trees.isCompleteTree(buildMerkle(l, h))
            ensures |collectLeaves(buildMerkle(l, h))| == power2(h - 1)
            ensures isDecoratedWithDiff(buildMerkle(l, h))
            ensures treeLeftmostLeavesMatchList(l, buildMerkle(l, h), 0)

        /** 
         *  Add element e to the tree.
         *
         *  @param  e   The element to add to the store.
         *
         *  @todo       This algorithm should maintain the invariant
         *              `diffRoot == root.v`.
         */
        method add(e: int)

            requires Trees.isCompleteTree(root)
            requires isValid()

            //  Store is not full
            requires |store| < power2(height - 1)

            //  Preserves tree height and completeness
            ensures height == old(height) == Trees.height(root) 
            ensures Trees.isCompleteTree(root)

            //  Store is updated
            ensures store == old(store) + [ e ]

            ensures |collectLeaves(root)| == power2(height - 1)

            //  diffRoot stores value of diff for store
            ensures isDecoratedWithDiff(root)
            ensures |store| <= power2(height - 1)
            ensures MerkleTrees.treeLeftmostLeavesMatchList(store, root, 0)

            //  The next one is not verified in the current version of this algo.
            ensures diffRoot == root.v

            // ensures isValid()

            modifies this
        {
            //  Update store
            store := store + [ e ] ;
            
            //  Define new tree for updated store
            root := buildMerkle(store, height);

            //  Compute the new diffRoot
            diffRoot := 0 ;
        }

    } 
}
