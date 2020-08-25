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

include "Trees2.dfy"
include "Helpers.dfy"
include "SeqOfBits.dfy"

/**
 *  Provide complete trees.
 *  
 *  A complete tree is a leaf of a node such that every outgoing branch
 *  has the same height.    
 */
module CompleteTrees { 

    import opened Trees
    import opened Helpers
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
            //  From a root node, a tree is complete if both children have same height
            case Node(_, lc, rc) => 
                && height(lc) == height(rc) 
                && isCompleteTree(lc) && isCompleteTree(rc)
    }

    //  Helper lemmas for complete trees.

    /**
     *  Relation between height and number of leaves in a complete tree.
     */
    lemma {:induction root} completeTreeNumberLemmas(root : Tree) 
        requires isCompleteTree(root)
        ensures |leavesIn(root)| == power2(height(root) - 1)
        ensures |nodesIn(root)| == power2(height(root)) - 1
    {   //  Thanks Dafny
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
        requires height(r) >= 2
        requires isCompleteTree(r)
        ensures match r
            case Node(_, lc, rc) => 
                |leavesIn(lc)| == |leavesIn(rc)| == power2(height(r) - 1) / 2
    {
        match r 
            case Node(_, lc, rc) =>
                completeTreesOfSameHeightHaveSameNumberOfLeaves(lc, rc);
    }

    /**
     *  Children of a node r in a complete tree of height >-= 2
     *  evenly partition leavesIn(r).
     */
    lemma {:induction r} childrenInCompTreesHaveHalfNumberOfLeaves(r : Tree, h : nat) 
        requires h == height(r) >= 2
        requires isCompleteTree(r)
        ensures |leavesIn(r)| == power2(h - 1)
        ensures match r
            case Node(_, lc, rc) => 
                leavesIn(lc) == leavesIn(r)[.. power2(h - 1) / 2]
                && leavesIn(rc) == leavesIn(r)[power2(height(r) - 1) / 2 ..]
    {
        if h == 2 {
            //  Thanks Dafny
        } else {
            match r
                case Node(_, lc, rc) => 
                    childrenInCompTreesHaveSameNumberOfLeaves(r);
        }
    }

    /**
     *  Children of indexed node are indexed by the corresponding sub-ranges.
     */
    lemma {:induction r} childrenCompTreeValidIndex(r : Tree, h : nat, i : nat)
        requires hasLeavesIndexedFrom(r, i)
        requires h == height(r) >= 2
        requires isCompleteTree(r)
        ensures match r
            case Node(_, lc, rc) => 
                hasLeavesIndexedFrom(lc, i)
                && hasLeavesIndexedFrom(rc, i + power2(height(r) - 1) / 2)
    {
        if h == 2 {
            match r
            case Node(_, lc, rc) => 
                calc == {
                    leavesIn(r) == [lc, rc];
                    leavesIn(r)[0] == lc;                
                    leavesIn(r)[0].index == i ;
                    leavesIn(r)[1] == rc;
                    leavesIn(r)[1].index == i + 1;
                    power2(height(r) - 1) / 2 == 1;
                }
        } else {
            childrenInCompTreesHaveHalfNumberOfLeaves(r, h);
        }
    }            
}