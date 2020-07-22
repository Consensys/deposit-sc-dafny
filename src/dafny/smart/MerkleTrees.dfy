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

module MerkleTrees {

    import opened Helpers
    import opened Trees

    /**
     *  Check that the levels in a tree are set according to the height - 1.
     *
     */
    predicate isMerkleLevelTree(root : Tree, level: nat) 
        requires isCompleteTree(root)
        decreases root
    {
        root.l == height(root) - 1
    }
    
    /**
     *
     *  Nodes in a Merkle tree can be indexed at each level from 1 to 2^(h - l) - 1.
     *  @todo   Check from 1 to 2^(h - l) - 1.
     *  @todo   Write the definition! for now consistently returns true ...
     */
    predicate isMerkleIndexedTree(root : Tree, level: nat) 
        requires isCompleteTree(root)
        decreases root
    {
         match root 
           case Leaf(_, l, i) => true
           case Node(_, lc, rc, l, i) => true
    }
     
    /**
     *  
     *  @param  l       A list of elements.
     *  @param  root    A tree.
     *  @param  default The default vakue for right-padding the tree leaves.
     *
     *  We assume collectLeaves return an indexed from left to right list of leaves.
     */
    predicate treeLeftmostLeavesMatchList<T>(l: seq<T>, root: Tree<T>, default: T)
        requires |l| <= |collectLeaves(root)|
    {
        forall i:: 
            (0 <= i < |l| ==> l[i] == collectLeaves(root)[i].v)
            && 
            (|l| <= i < |collectLeaves(root)|  ==> collectLeaves(root)[i].v == default)
    }
}
