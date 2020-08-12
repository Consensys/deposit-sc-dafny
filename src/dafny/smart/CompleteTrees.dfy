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
     *  Each type T has a default value.
     */
    function method default<T>() : T 

    type compTree<T> = r: Tree<T> | isCompleteTree(r) witness Leaf(default<T>())
 
    /**
     *  Complete trees.
     *
     *  @param  root    The root node of the tree.
     *  @returns        True if and only if the tree rooted at root is complete
     */
    predicate isCompleteTree(root : Tree) 
        decreases root
    {
        match root 
            //  A leaf is a complete tree
            case Leaf(_) => true
            //  From a root node, a tree is complete if both children have same height
            case Node(_, lc, rc) => 
                && height(lc) == height(rc) 
                && isCompleteTree(lc) && isCompleteTree(rc)
    }

    
    //  Helper lemmas for complete trees.

    /**
     *  Relation between height and number of leaves in a complete tree.
     */
    lemma {:induction root} completeTreeNumberLemmas(root : compTree) 
        ensures |leavesIn(root)| == power2(height(root) - 1)
        ensures |nodesIn(root)| == power2(height(root)) - 1
    {   //  Thanks Dafny
    }

    /**
     *  Two complete tree of same height have same number of leaves.
     */
    lemma {:induction r1, r2} completeTreesOfSameHeightHaveSameNumberOfLeaves(r1: compTree, r2: compTree) 
        ensures height(r1) == height(r2) ==> |leavesIn(r1)| == |leavesIn(r2)|
    {   //  Thanks Dafny
    }

    /**
     *  Children of a node in a complete tree have same number of leaves.
     */
    lemma {:induction r} completeTreesLeftRightHaveSameNumberOfLeaves(r : compTree) 
        requires height(r) >= 2
        ensures match r
            case Node(_, lc, rc) => 
                |leavesIn(lc)| == |leavesIn(rc)| == power2(height(r) - 1) / 2
    {
        match r 
            case Node(_, lc, rc) =>
                completeTreesOfSameHeightHaveSameNumberOfLeaves(lc,rc);
    }

    lemma {:induction r} completeTreesLeftRightChildrenLeaves(r : compTree, h : nat) 
        requires h == height(r) >= 2
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
                    completeTreesLeftRightHaveSameNumberOfLeaves(r);
        }
    }

 

}