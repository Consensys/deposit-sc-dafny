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

/**
 *     Provide complete trees.
 */
module CompleteTrees { 

    import opened Trees
    import opened Helpers

    /**
     *  Complete trees.
     *
     *  @param  root    The root node of the tree.
     *  @returns        True if and only if the tree rooted at root is complete
     */
    predicate isCompleteTree(root : ITree) 
        decreases root
    {
        match root 
            //  A leaf is a complete tree
            case ILeaf(_, _) => true
            //  From a root node, a tree is complete if both children have same height
            case INode(_, lc, rc, _) => 
                && height(lc) == height(rc) 
                && isCompleteTree(lc) && isCompleteTree(rc)
    }

    
    //  Helper lemmas for complete trees.

    /**
     *  Relation between height and number of leaves in a complete tree.
     */
    lemma {:induction root} completeTreeNumberLemmas(root : ITree) 
        ensures isCompleteTree(root) ==> |leavesIn(root)| == power2(height(root) - 1)
        ensures isCompleteTree(root) ==> |nodesIn(root)| == power2(height(root)) - 1
    {   //  Thanks Dafny
    }

    /**
     *  Two complete tree of same height have same number of leaves.
     */
    lemma {:induction r1, r2} completeTreesOfSameHeightHaveSameNumberOfLeaves(r1: ITree, r2: ITree) 
        requires isCompleteTree(r1)
        requires isCompleteTree(r2)
        ensures height(r1) == height(r2) ==> |leavesIn(r1)| == |leavesIn(r2)|
    {   //  Thanks Dafny
    }

    /**
     *  Children of a node in a complete tree have same number of leaves.
     */
    lemma {:induction r} completeTreesLeftRightHaveSameNumberOfLeaves(r : ITree) 
        requires isCompleteTree(r)
        requires height(r) >= 2
        ensures match r
            case INode(_, lc, rc, _) => 
                |leavesIn(lc)| == |leavesIn(rc)| == power2(height(r) - 1) / 2
    {
        match r 
            case INode(_, lc, rc, _) =>
                completeTreesOfSameHeightHaveSameNumberOfLeaves(lc,rc);
    }

    lemma {:induction r} completeTreesLeftRightChildrenLeaves(r : ITree, h : nat) 
        requires isCompleteTree(r)
        requires h == height(r) >= 2
        ensures |leavesIn(r)| == power2(h - 1)
        ensures match r
            case INode(_, lc, rc, _) => 
                leavesIn(lc) == leavesIn(r)[.. power2(h - 1) / 2]
                && leavesIn(rc) == leavesIn(r)[power2(height(r) - 1) / 2 ..]
    {
        if h == 2 {
            //  Thanks Dafny
        } else {
            match r
                case INode(_, lc, rc, _) => 
                    completeTreesLeftRightHaveSameNumberOfLeaves(r);
        }
    }

 

}