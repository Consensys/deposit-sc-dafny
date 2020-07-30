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
include "Trees2.dfy"
include "MerkleTrees.dfy"

module DiffTree {

    import opened Helpers
    import opened Trees
    import opened MerkleTrees

    //  Trees holding integer values as attribute.
    type Intnode = Tree<int>

    /** 
     *  Difference between two integers.
     *
     *  @note:  This could be inlined in the predicate
     *          isDecoratedWithDiff, but we may use another 
     *          function later, so we factor it out.
     */
    function method diff(a: int, b : int) : int 
    {
        a - b
    }
    
    /**
     *  Check that a decorated tree correctly stores the diff attribute. 
     */
    predicate isDecoratedWithDiff(r: ITree<int>) 
    {
        isDecoratedWith(diff, r)
    } 

    /**
     *  Incremental algorithm.
     *
     *  @todo   Add data structures and complete method add to
     *          correctly compute diffRoot. 
     */
    class IntTree {

        /**  The root tracking the Merkle Tree. */
        ghost var root : ITree<int>

        /** Height of the tree */
        var h : nat 

        /** diffRoot, the value of diff on the root. */
        var diffRoot : int

        /** Number of elements in the tree. */
        // var counter : nat

        /** The list of ints stored in the tree.  */
        ghost var store : seq<int>

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
            && h == height(root) 
            && 0 <= |store| <= power2(h - 1)
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
         *  Defines the Int Tree associated with a given sequence.
         *  
         *  @note   T   his function does not compute the tree but rather
         *              defines its properties: correctly stores the attribute
         *              `diff` and the leftmost |l| leaves store l.
         *
         *  @param  l   
         */
        // function buildMerkle(l: seq<int>, h : nat) : Tree<int> 
        //     requires h >= 1
        //     /** Tree has enough leaves to store `l`. */
        //     requires |l| <= power2(h - 1)      

        //     ensures height(buildMerkle(l, h)) == h
        //     ensures isCompleteTree(buildMerkle(l, h))
        //     ensures |collectLeaves(buildMerkle(l, h))| == power2(h - 1)
        //     ensures isDecoratedWithDiff(buildMerkle(l, h))
        //     ensures treeLeftmostLeavesMatchList(l, buildMerkle(l, h), 0)

        /**
         *  The tree decorated with zeroes.
         *  
         *  @param  r   A tree.
         *  @returns    True if and only if all values are zero.
         */
        predicate isZeroTree(r : ITree<int>) 
        {
            isConstant(r, 0)
        }

        /**
         *  Equivalent characterisation of zero trees.
         */
        lemma {:induction r} isZeroTreeiffAllNodesZero(r : ITree<int>) 
             ensures (forall l :: l in nodesIn(r) ==> l.v == 0) <==> isZeroTree(r)
        {   //  Thanks Dafny
        } 

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
         *  If all leaves are zero and tree is decorated with diff, then
         *  all nodes are zero.
         */
        lemma {:induction r} allLeavesZeroImplyAllNodesZero(r: ITree<int>) 
            requires isDecoratedWithDiff(r)
            requires forall l :: l in leavesIn(r) ==> l.v == 0
            ensures forall l :: l in nodesIn(r) ==> l.v == 0 
        {   //  Thanks Dafny
        }

        /**
         *  Merkle tree of height 1 with empty list is Leaf(0).
         */
        // lemma merkleTreeHeightOneZero() 
        //     ensures buildMerkle([], 1) == Leaf(0)
        // {
        //     assert(buildMerkle([], 1).Leaf?);
        //     match buildMerkle([], 1)
        //         case Leaf(v) => 
        //             assert (Leaf(v) in collectLeaves(buildMerkle([], 1)));
        // }

        // lemma foo15(p: seq<bool>, r: Tree<int>, l : seq<int>, h : nat)


        /**
         *  Vakues of the nodes on the right of a path to e in Merkle(l :+ e,h)
         *  are all zeroes.
         */
        // lemma nodesOnRightZero(p: seq<bool>, r: Tree<int>, l : seq<int>, h : nat)
        //     requires h == height(r) >= 1
        //     requires |l| <= power2(h - 1)
        //     requires r == buildMerkle(l, h)
        //     requires pathToLeafIndex(p) == |l|
        //     requires |p| == h - 1
        //     ensures forall n :: n in nodesRightOf(p, r) ==> n.v == 0 
        // {
        //     if h == 1 {
        //         //  Thanks Dafny
        //     }
        //     else {
        //         match r 
        //             case Node(_, lc, rc) =>
        //     }
        // }

        /**
         *  The value of diff at the root of a well decorated tree is the value of
         *  the tree.
         */
        function hash_tree_root(r: ITree<int>) : int 
            requires isCompleteTree(r)
            requires isDecoratedWithDiff(r) 
        {
            r.v
        }

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
            // root := buildMerkle(store, h);

            //  Compute the new diffRoot
            diffRoot := 0 ;
        }

        // function method foo(p : seq<bool>, levelVal : seq<int>, lastVal: int) : int 
        //     requires |p| == |levelVal|
        //     decreases p
        // {
        //     if |p| == 0 then
        //         lastVal
        //     else if p[0] then
        //         //  child was on the left
        //         foo(p[1..], levelVal[1..], diff(lastVal, levelVal[0]))
        //     else 
        //         //  child was on the right
        //         foo(p[1..], levelVal[1..], diff(levelVal[0], lastVal))
        // }

        // method foo2(p: seq<bool>, r: Tree<int>) returns (r' : Tree<int>)
        //     requires |p| == height(r) - 1
        //     requires isCompleteTree(r)
        //     requires forall i :: 0 <= i < |p| ==> isDecoratedWithDiff(leftRight(p, r)[i])

        //     ensures isDecoratedWithDiff(r')
        // {
        //     r' := r;
        //     //  compute attribute on path `p`.
        // }

    } 
}
