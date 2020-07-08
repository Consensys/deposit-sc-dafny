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
     *  Whether the tree defined by a node is a Merkle Tree of height `h`.
     */
    predicate isCompleteTree<T>(root : Node<T>, h : nat) 
        requires h == height(root)
        decreases h
    {
        match root 
            //  a leaf, level 0 is a MT of height 1
            case Leaf(_, l, _) => l == h - 1 == 0
            //  A node, level l, is a MT of height h if both children are MTs of height h - 1
            case Node(_, lc, rc, l, _) => 1 <= l == h - 1 
                && height(lc) == height(rc) == h - 1
                && isCompleteTree(lc, h - 1) && isCompleteTree(rc, h - 1)
    }

    /**
     *  Check that the levels in a tree are set accordingly.
     *
     */
    predicate isMerkleLevelTree<T>(root : Node<T>, level: nat) 
        requires isCompleteTree(root, height(root))
        decreases root
    {
         match root 
           case Leaf(_, l, _) => l == level == 0
           case Node(_, lc, rc, l, _) => l >= 0 && isMerkleLevelTree(lc, l - 1) && isMerkleLevelTree(rc,l - 1)
    }
    
    /**
     *  The level of root is height - 1 for a correctly levelled tree.
     */
    lemma {:induction root} levelOfRoot<T>(root : Node<T>) 
        requires isCompleteTree(root, height(root))
        requires  isMerkleLevelTree(root, height(root) - 1)
        ensures root.l == height(root) - 1
    {   //  Thanks Dafny
    }    

    /**
     *
     *  Nodes in a Merkle tree can be indexed at each level from 1 to 2^(h - l) - 1.
     */
    predicate isMerkleIndexedTree<T>(root : Node<T>, level: nat) 
        requires isCompleteTree(root, height(root))
        decreases root
    {
         match root 
           case Leaf(_, l, _) => true
           case Node(_, lc, rc, l, _) => true
    }
    
    // lemma {:induction root} levelOfRoot<T>(root : Node<T>) 
    //     requires isCompleteTree(root, height(root))
    //     requires  isMerkleLevelTree(root, height(root) - 1)
    //     ensures root.l == height(root) - 1
    // {   //  Thanks Dafny
    // }    
    
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
            case Node(_, lc, rc, _, _) =>  collectLeaves<T>(lc) + collectLeaves<T>(rc) 
    }
    
    /**
     *  In a MerkleTree, all the levels are between 0 and h - 1
     */
    // lemma boundedLevels<T>(root : Node<T>, h : nat) 
    //     requires isMerkleTree(root, h)
    //     ensures 
    // {

    // }

    /**
     *  A binary Merkle Tree of height h has 2^h - 1 nodes.
     */
    lemma {:induction root, h} numberOfNodesInCompleteTree<T>(root : Node<T>, h : nat)
        requires h == height(root)
        requires isCompleteTree(root, h)
        ensures |collectNodes(root)| == power2(h) - 1
    {   //  Thanks Dafny
    }

    /**
     *  The number of leaves in a complete tree.
     */
    lemma {:induction root, h} numberOfLeavesInCompleteTree<T>(root : Node<T>, h : nat)
        requires h == height(root)
        requires isCompleteTree(root, h)
        ensures |collectLeaves(root)| == power2(h - 1)       
    {   //  Thanks Dafny
    } 




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
