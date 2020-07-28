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
     */
    datatype Tree<T> = 
            Leaf(v: T)
        |   Node(v: T, left: Tree, right: Tree)

    /**
     *  Height of a tree.
     */
    function height(root : Tree) : nat 
        ensures height(root) >= 1
        decreases root
    {
        match root 
            //  a leaf, level 0 is a MT of height 1
            case Leaf(_) => 1
            //  A node, level l, is a MT of height h if both children are MTs of height h - 1
            case Node(_, lc, rc) => 1 + max(height(lc), height(rc))
    }

    /**
     *  The node at the end of a path.
     *
     *  @param  p   A path (left/right).
     *  @param  r   A complete binary tree.
     *
     *  @returns    The node of the tree that is the target of path `p`.
     */
    function nodeAt(p : seq<bool>, r: Tree) : Tree
        requires |p| < height(r) 
        requires isCompleteTree(r)
        decreases p
    {
        if |p| == 0 then  
            r
        else 
            // r must be a node as height(r) > |p| >= 1
            assert(r.Node?);
            match r 
                case Node(_, lc, rc) => 
                        if p[0] then
                        nodeAt(p[1..], lc)
                    else 
                        nodeAt(p[1..], rc)
    }

    /**
     *  The nodes on each side of the path to a leaf.
     *
     *  @param  p   A path (left/right).
     *  @param  r   A complete binary tree.
     *  @returns    The nodes on the sides of the path `p`.
     */
    function leftRight(p : seq<bool>, r: Tree) : seq<Tree>
        requires |p| == height(r) - 1
        requires isCompleteTree(r)
        ensures |leftRight(p, r)| == |p|
        decreases p
    {
        match r 
            case Leaf(_) => []

            case Node(_, lc, rc) => 
                if p[0] then
                    [lc] + leftRight(p[1..], lc)
                else 
                    [rc] + leftRight(p[1..], rc)
    }

    /**
     *  The nodes of a tree (pre-order traversal).    .
     *
     *  @param  root    The root of the tree.
     *
     *  @return         The sequence of nodes/leaves that corresponds to the pre-order 
     *                  (node, left, right) traversal of a tree.
     *  @todo           We don't really need that but only the number of nodes.
     */
    function method collectNodes(root : Tree) : seq<Tree>
        decreases root
    {
        match root 
            case Leaf(_) => [ root ] 
            case Node(_, lc, rc) =>  [ root ] + collectNodes(lc) + collectNodes(rc) 
    }

    /**
     *  The leaves of a tree (in-order traversal).
     *  
     *  @param  root    The root node of the tree.
     *
     *  @return         The leaves as a sequence from left to right in-order 
     *                  traversal (left, node, right).
     *
     *  @todo           We don't really need that but only the values of the leaves.
     *
     */
    function method collectLeaves(root : Tree) : seq<Tree>
        ensures forall i :: 0 <= i < |collectLeaves(root)| ==>  collectLeaves(root)[i].Leaf?
        decreases root
    {
        match root 
            case Leaf(_) => [ root ] 
            case Node(_, lc, rc) =>  
                collectLeaves(lc) + collectLeaves(rc) 
    }
    
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
    
    //  Helpers lemmas.

    /**
     *  Relation between height and number of leaves in a complete tree.
     */
    lemma {:induction root} completeTreeNumberOfLeaves(root : Tree) 
        ensures isCompleteTree(root) ==> |collectLeaves(root)| == power2(height(root) - 1)
    {   //  Thanks Dafny
    }

    /**
     *  Relation between height and number of nodes in a complete tree.
     */
    lemma {:induction root} completeTreeNumberOfNodes(root : Tree) 
        ensures isCompleteTree(root) ==> |collectNodes(root)| == power2(height(root)) - 1
    {   //  Thanks Dafny
    }
     
} 
