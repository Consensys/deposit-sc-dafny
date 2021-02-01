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

include "Trees.dfy"
include "../helpers/Helpers.dfy"
include "../helpers/SeqHelpers.dfy"
include "../seqofbits/SeqOfBits.dfy"

/**
 *  Provide complete trees.
 *  
 *  A complete tree is a leaf or a node such that every outgoing branch
 *  has the same height.    
 *
 *  It is sometimes called perfect trees in the literature.
 */
module CompleteTrees { 

    import opened Trees
    import opened Helpers
    import opened SeqHelpers
    import opened SeqOfBits

    /**
     *  Complete trees.
     *
     *  @param  root    The root node of the tree.
     *  @returns        True if and only if the tree rooted at root is complete.
     */
    predicate isCompleteTree(root : Tree) 
        decreases root
    {
        match root 
            //  A leaf is a complete tree
            case Leaf(_, _) => true
            //  From a root node, a tree is complete if both children are complete.
            case Node(_, lc, rc) => 
                && height(lc) == height(rc) 
                && isCompleteTree(lc) && isCompleteTree(rc)
    }

    /**
     *  Collect first k leaves in a tree.
     */
    function {:opaque} takeLeavesIn<T>(r : Tree<T>, k : nat) : seq<Tree<T>>
        requires isCompleteTree(r)
        requires k <= |leavesIn(r)|
        ensures |takeLeavesIn(r, k)| == k 
    {
        completeTreeNumberLemmas(r);
        take(leavesIn(r), k)
    }

    /**
     *  Drop first k leaves in a tree.
     */
    function {:opaque} dropLeavesIn<T>(r : Tree<T>, k : nat) : seq<Tree<T>>
        requires isCompleteTree(r)
        requires k <= |leavesIn(r)|
        ensures |dropLeavesIn(r, k)| == |leavesIn(r)| - k
    {
        completeTreeNumberLemmas(r);
        drop(leavesIn(r), k)
    }

    //  Helper lemmas for complete trees.

    /**
     *  Relation between height and number of leaves in a complete tree.
     */
    lemma {:induction root} completeTreeNumberLemmas(root : Tree) 
        requires isCompleteTree(root)
        ensures |leavesIn(root)| == power2(height(root))
        ensures |nodesIn(root)| == power2(height(root) + 1) - 1
    {   //  Thanks Dafny
        reveal_power2();
    }

    /**
     *  Two complete tree of same height have same number of leaves.
     */
    lemma {:induction r1, r2} completeTreesOfSameHeightHaveSameNumberOfLeaves(r1: Tree, r2: Tree) 
        requires isCompleteTree(r1)
        requires isCompleteTree(r2)
        ensures height(r1) == height(r2) ==> |leavesIn(r1)| == |leavesIn(r2)|
    {   //  Thanks Dafny
    }

    /**
     *  Children of a node in a complete tree have same number of leaves.
     */
    lemma {:induction r} childrenInCompTreesHaveSameNumberOfLeaves(r : Tree) 
        requires height(r) >= 1
        requires isCompleteTree(r)
        ensures match r
            case Node(_, lc, rc) => 
                |leavesIn(lc)| == |leavesIn(rc)| == power2(height(r)) / 2
    {
        reveal_power2();
        match r 
            case Node(_, lc, rc) =>
                completeTreesOfSameHeightHaveSameNumberOfLeaves(lc, rc);
    }

    /**
     *  Height of children in complete tees.
     */
     lemma {:induction r} childrenInCompTreesHaveHeightMinusOne(r : Tree) 
        requires height(r) >= 1
        requires isCompleteTree(r)
        ensures match r
            case Node(_, lc, rc) => 
                height(lc) == height(rc) == height(r) - 1
    {   //  Thanks Dafny
    }

    /**
     *  Children of a node r in a complete tree of height >= 1
     *  evenly partition leavesIn(r).
     */
    lemma {:induction r} childrenInCompTreesHaveHalfNumberOfLeaves(r : Tree, h : nat) 
        requires h == height(r) >= 1
        requires isCompleteTree(r)
        ensures |leavesIn(r)| == power2(h)
        ensures match r
            case Node(_, lc, rc) => 
                (leavesIn(lc) == leavesIn(r)[.. power2(height(r)) / 2] 
                 == takeLeavesIn(r, power2(height(r)) / 2))
                && (leavesIn(rc) == leavesIn(r)[power2(height(r)) / 2 ..]
                 == dropLeavesIn(r, power2(height(r)) / 2))
    {
        reveal_power2();
        reveal_takeLeavesIn();
        reveal_dropLeavesIn();
        childrenInCompTreesHaveSameNumberOfLeaves(r);
    }

    /**
     *  Children of indexed node are indexed by the corresponding sub-ranges.
     */
    lemma {:induction r} childrenCompTreeValidIndex(r : Tree, h : nat, i : nat)
        requires hasLeavesIndexedFrom(r, i)
        requires h == height(r) >= 1
        requires isCompleteTree(r)
        ensures match r
            case Node(_, lc, rc) => 
                hasLeavesIndexedFrom(lc, i)
                && hasLeavesIndexedFrom(rc, i + power2(height(r)) / 2)
    {
        childrenInCompTreesHaveHalfNumberOfLeaves(r, h);
    }       
}