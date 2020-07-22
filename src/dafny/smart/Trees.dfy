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

/**
 *  Provide tree decorated with value, level and index.
 */
module Trees {

    import opened Helpers

    /** Indexed/leveled Binary trees.
     *
     *  Values are in a domain `T`.
     *  
     *  @param  v   The value associated with a node.
     *  @param  l   This ghost variable is the level of a node.
     *              It is 0 for leaves.
     *  @param  i   The index of a child at a given level.
     */
    datatype Tree<T> = 
            Leaf(v: T, ghost l: nat, ghost i: nat)
        |   Node(v: T, left: Tree, right: Tree, ghost l: nat, ghost i: nat)

    /**
     *  Height of a tree.
     */
    function height(root : Tree) : nat 
        ensures height(root) >= 1
        decreases root
    {
        match root 
            //  a leaf, level 0 is a MT of height 1
            case Leaf(_, _, _) => 1
            //  A node, level l, is a MT of height h if both children are MTs of height h - 1
            case Node(_, lc, rc, _, _) => 1 + max(height(lc), height(rc))
    }

    /**
     *  The nodes of a tree (pre-order traversal).    .
     *
     *  @param  root    The root of the tree.
     *
     *  @return         The sequence of nodes/leaves that corresponds to the pre-order 
     *                  (node, left, right) traversal of a tree.
     */
    function method collectNodes(root : Tree) : seq<Tree>
        decreases root
    {
        match root 
            case Leaf(_, _, _) => [ root ] 
            case Node(_, lc, rc, _, _) =>  [ root ] + collectNodes(lc) + collectNodes(rc) 
    }

    /**
     *  The leaves of a tree (in-order traversal).
     *  
     *  @param  root    The root node of the tree.
     *
     *  @return         The leaves as a sequence from left to right in-order traversal (left, node, right).
     *
     */
    function method collectLeaves(root : Tree) : seq<Tree>
        ensures forall i :: 0 <= i < |collectLeaves(root)| ==>  collectLeaves(root)[i].Leaf?
        decreases root
    {
        match root 
            case Leaf(_, _, _) => [ root ] 
            case Node(_, lc, rc, _, _) =>  
                collectLeaves(lc) + collectLeaves(rc) 
    }
    
    /**
     *  Whether the tree rooted at root is complete.
     *
     *  @param  root    The root node of the tree.
     */
    predicate isCompleteTree(root : Tree) 
        decreases root
    {
        match root 
            //  A leaf is a complete tree
            case Leaf(_, _, _) => true
            //  From a root node, a tree is complete if both children have same height
            case Node(_, lc, rc, _, _) => 
                && height(lc) == height(rc) 
                && isCompleteTree(lc) && isCompleteTree(rc)
    }

    /**
     *  Relation between height and number of leaves in a complete tree.
     */
    lemma {:induction root} completeTreeNumberOfLeaves(root : Tree) 
        requires isCompleteTree(root)
        ensures |collectLeaves(root)| == power2(height(root) - 1)
    {   //  Thanks Dafny
    }

    /**
     *  Relation between height and number of nodes in a complete tree.
     */
    lemma {:induction root} completeTreeNumberOfNodes(root : Tree) 
        requires isCompleteTree(root)
        ensures |collectNodes(root)| == power2(height(root)) - 1
    {   //  Thanks Dafny
    }
     
} 
