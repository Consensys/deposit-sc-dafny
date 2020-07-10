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

module DepositSmartContract {

    import opened Helpers

    /** Merkle Binary trees.
     *
     *  Values are in a domain `T`.
     *  
     *  @param  l   This ghost variable is the level of a node.
     *              It is 0 for leaves.
     *  @param  i   The index of a child at a given level.
     */
    datatype Node<T> = 
            Leaf(v: T, ghost l: nat, ghost i: nat)
        |   Node(v: T, left: Node, right: Node, ghost l: nat, ghost i: nat)

    /**
     *  Height of a tree.
     */
    function height<T>(root : Node<T>) : nat 
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
     *  We return a sequence of nodes.
     *
     *  @note   We may not use a set for collectting the nodes, as it is possible that
     *          that two nodes in subtrees are equal.
     */
    function collectNodes<T>(root : Node<T>) : seq<Node<T>>
        decreases root
    {
        match root 
            case Leaf(_, _, _) => [ root ] 
            case Node(_, lc, rc, _, _) =>  [ root ] + collectNodes<T>(lc) + collectNodes<T>(rc) 
    }

    /**
     *  We return the leaves as a sequence from left to right.
     *
     */
    function collectLeaves<T>(root : Node<T>) : seq<Node<T>>
        decreases root
    {
        match root 
            case Leaf(_, _, _) => [ root ] 
            case Node(_, lc, rc, _, _) =>  
                collectLeaves<T>(lc) + collectLeaves<T>(rc) 
    }
    
    /**
     *  Whether the tree defined by a node is a Merkle Tree of height `h`.
     */
    predicate isCompleteTree<T>(root : Node<T>) 
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
     *  Check that the levels in a tree are set according to the height - 1.
     *
     */
    predicate isMerkleLevelTree<T>(root : Node<T>, level: nat) 
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
    predicate isMerkleIndexedTree<T>(root : Node<T>, level: nat) 
        requires isCompleteTree(root)
        decreases root
    {
         match root 
           case Leaf(_, l, i) => true
           case Node(_, lc, rc, l, i) => true
    }
     
    /**
     *  Relation between heigth and number of leaves in a complete tree.
     */
    lemma {:induction root} completeTreeNumberOfLeaves<T>(root : Node<T>) 
        requires isCompleteTree(root)
        ensures |collectLeaves(root)| == power2(height(root) - 1)
    {   //  Thanks Dafny
    }

    /**
     *  Relation between heigth and number of nodes in a complete tree.
     */
    lemma {:induction root} completeTreeNumberOfNodes<T>(root : Node<T>) 
        requires isCompleteTree(root)
        ensures |collectNodes(root)| == power2(height(root)) - 1
    {   //  Thanks Dafny
    }

    //  Trees holding integer attributes
    type Intnode = Node<int>

    /** 
     *  Difference between two integers.
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
     *  
     */

/*
 * fun init() -> unit:
 *     i: int = 0
 *     while i < TREE_HEIGHT - 1:
 *         zerohashes[i+1] = hash(zerohashes[i], zerohashes[i])
 *         i += 1
 */

/*
 * fun deposit(value: int) -> unit:
 *     assert deposit_count < 2^TREE_HEIGHT - 1
 *     deposit_count += 1
 *     size: int = deposit_count
 *     i: int = 0
 *     while i < TREE_HEIGHT - 1:
 *         if size % 2 == 1:
 *             break
 *         value = hash(branch[i], value)
 *         size /= 2
 *         i += 1
 *     branch[i] = value
 */

/*
 * fun get_deposit_root() -> int:
 *     root: int = 0
 *     size: int = deposit_count
 *     h: int = 0
 *     while h < TREE_HEIGHT:
 *         if size % 2 == 1: # size is odd
 *             root = hash(branch[h], root)
 *         else:             # size is even
 *             root = hash(root, zerohashes[h])
 *         size /= 2
 *         h += 1
 *     return root
 */


}
