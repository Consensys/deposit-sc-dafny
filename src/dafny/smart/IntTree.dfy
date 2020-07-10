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

include "Trees.dfy"
include "MerkleTrees.dfy"

module DiffTree {

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
    {
        match root
            case Leaf(v, _, _) => true

            case Node(v, lc, rc, _, _) => v == diff(lc.v, rc.v)
    }

    /**
     *  Incremental algorithm.
     */
    class IntTree {

        constructor()

        method incrDiffAlgo(root: Node<int>, l: seq<int>, e: int) returns (root' : Node<int>) 
            requires isCompleteTree(root)
            requires |l| < |collectLeaves(root)|
            requires MerkleTrees.treeLeftmostLeavesMatchList(l, root, 0)

            ensures isCompleteTree(root')
            ensures height(root') == height(root)
            ensures MerkleTrees.treeLeftmostLeavesMatchList(l + [e], root', 0)
        {

        }

    } 

}
