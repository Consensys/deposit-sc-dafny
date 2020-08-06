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
 *  Provide tree decorated with value.
 */
module Trees {

    import opened Helpers

    /** Binary trees.
     *
     *  Values are in a domain `T`.
     *  
     *  @tparam T   The type of values attached to the nodes.
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
     *  @param  p   A path (left/right) in a binary tree.
     *  @param  r   A complete binary tree.
     *
     *  @returns    The node of the tree that is the target of path `p`.
     */
    function nodeAt(p : seq<bool>, r: Tree) : Tree
        requires |p| < height(r) 
        requires isCompleteTree(r)
        ensures nodeAt(p, r) in collectNodes(r)
        decreases p
    {
        if |p| == 0 then  
            r
        else 
            // r must be a node as height(r) > |p| >= 1
            match r 
                case Node(_, lc, rc) => 
                    nodeAt(p[1..], if !p[0] then lc else rc)
    }

    /**
     *  Collect nodes on the right hand-side of a full path.
     *  
     *  @param  p   A path.
     *  @param  r   A complete binary tree.
     */
    function nodesRightOf(p: seq<bool>, r : Tree) : seq<Tree> 
        requires |p| == height(r) - 1 
        requires isCompleteTree(r)
        decreases p
    {
        if |p| == 0 then
            []
        else
            match r 
                case Node(_, lc, rc) =>
                    if !p[0] then
                        collectNodes(rc) + nodesRightOf(p[1..], lc)
                    else 
                        nodesRightOf(p[1..], rc)
    }

    /**
     *  The node at a depth height(r) - 1 is a leaf.
     */
    lemma {:induction p, r} nodeAfterFullPathIsLeaf(p : seq<bool>, r : Tree) 
        requires |p| == height(r) - 1 
        requires isCompleteTree(r)
        ensures nodeAt(p, r).Leaf?
    {   //  Thanks Dafny
    }

    /**
     *  The leaf that corresponds to a path of length height(r) - 1.
     *
     *  @param  p   A full path.
     *  @param  t   A complete binary tree.
     *  @returns    The leaf at the end of the path.
     */
    function leafAt(p : seq<bool>, r: Tree) : Tree
        requires |p| == height(r) - 1 
        requires isCompleteTree(r)
        ensures leafAt(p, r).Leaf?
        ensures leafAt(p, r) in collectLeaves(r)
    {
        //  Proof of post-condition
        nodeAfterFullPathIsLeaf(p, r);
        nodeAt(p, r)
    }

    /**
     *  Index of a leaf on a given path.
     */
    // function leafInOrderIndex(p : seq<bool>) : nat 
    //     ensures 0 <= leafInOrderIndex(p, r) < power2(|p|)
    // {
    //     bitListToNat(p, 0)
    // }
    
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
        /** All the collected nodes are leaves. */
        ensures forall i :: 0 <= i < |collectLeaves(root)| ==>  collectLeaves(root)[i].Leaf?
        /** All the leaves are collected. */
        ensures forall n :: n in collectNodes(root) && n.Leaf? ==> n in collectLeaves(root)
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

    // lemma collectLeavesIndices(r : Tree, i : nat) 
    //     requires isCompleteTree(r)
    //     requires r.Node?
    //     requires 0 <= i < power2(height(r) - 1) / 2
    //     ensures height(r) >= 2
    //     ensures match r 
    //         case Node(_, lc, rc) =>  
    //             collectLeaves(r)[i] == collectLeaves(lc)[i]
    // {
    //     match r 
    //         case Node(_, lc, rc) =>  
    //             // completeTreeNumberOfLeaves(r);
    //             completeTreeNumberOfLeaves(lc);
    //             assert( power2(height(r) - 1) / 2 == power2(height(r) - 2));
    //             assert( i < power2(height(lc) - 1));
    // }

    // lemma foo1(r : Tree, i : nat)
    //     requires isCompleteTree(r)
    //     requires r.Node?
    //     requires 0 <= i < power2(height(r) - 1) / 2
    //     ensures height(r) >= 2
    //     ensures match r 
    //         case Node(_, lc, _) =>
    //             collectLeaves(r)[i] in collectLeaves(lc)
    // {

    // }

    /**
     *  Two complete tree of same height have same number of leaves.
     */
    lemma {:induction r1, r2} completeTreesOfSameHeightHaveSameNumberOfLeaves(r1: Tree, r2: Tree) 
        requires isCompleteTree(r1)
        requires isCompleteTree(r2)
        ensures height(r1) == height(r2) ==> |collectLeaves(r1)| == |collectLeaves(r2)|
    {   //  Thanks Dafny
    }

    /**
     *  Children of a node in a complete tree have same number of leaves.
     */
    lemma {:induction r} completeTreesLeftRightHaveSameNumberOfLeaves(r : Tree) 
        requires isCompleteTree(r)
        requires height(r) >= 2
        ensures match r
            case Node(_, lc, rc) => 
                |collectLeaves(lc)| == |collectLeaves(rc)| == power2(height(r) - 1) / 2
    {
        match r 
            case Node(_, lc, rc) =>
                completeTreesOfSameHeightHaveSameNumberOfLeaves(lc,rc);
    }

    /**
     *  Split of sequences.
     */
    lemma splitSeq<T>(s: seq<T>, t: seq<T>, u : seq<T>)
        requires s == t + u
        ensures s[..|t|] == t
        ensures s[|t|..] == u
    {   //  Thanks Dafny
    }

    /**
     *  Leaves indices in complete trees.   
     */
    lemma {:induction r} leavesIndicesInCompleteTrees(r: Tree, i : nat)
        requires isCompleteTree(r)
        requires 0 <= i < power2(height(r) - 1)
        requires height(r) >= 2
        ensures |collectLeaves(r)| == power2(height(r) - 1)
        ensures match r 
            case Node(_, lc, rc) => 
                collectLeaves(r)[..power2(height(r) - 1) / 2] == collectLeaves(lc) 
                &&
                collectLeaves(r)[power2(height(r) - 1) / 2..] == collectLeaves(rc)
    {
       match r 
            case Node(_, lc, rc) => 
                //  
                completeTreesLeftRightHaveSameNumberOfLeaves(r);
                splitSeq(collectLeaves(r), collectLeaves(lc), collectLeaves(rc)); 
    }
     
    /**
     *  Location of leaf given first digit in the path.
     */
    lemma {:induction r} firstDigitDeterminesNodesLoc(p : seq<bool>, r : Tree) 
        requires isCompleteTree(r)
        requires 1 <= |p| <= height(r) - 1
        requires height(r) >= 2
        ensures match r
            case Node(_, lc, rc) => 
                (!p[0] &&  nodeAt(p, r) in collectNodes(lc))
                ||
                (p[0] && nodeAt(p, r) in collectNodes(rc))
    {   //  Thanks Dafny.
    }

    lemma {:induction r} firstDigitDeterminesLeafLoc(p : seq<bool>, r : Tree) 
        requires isCompleteTree(r)
        requires |p| == height(r) - 1
        requires height(r) >= 2
        ensures match r
            case Node(_, lc, rc) => 
                (!p[0] && leafAt(p, r) in collectLeaves(lc))
                ||
                (p[0] && leafAt(p, r) in collectLeaves(rc))
    {   //  Thanks Dafny
    }

    lemma foo45(p : seq<bool>, r : Tree) 
        requires isCompleteTree(r)
        requires |p| == height(r) - 1
        requires height(r) >= 2
        requires !p[0]
        ensures match r
            case Node(_, lc, _) => leafAt(p, r) in collectLeaves(lc)
    {
        firstDigitDeterminesLeafLoc(p, r);
    }

    lemma {:induction p} foo13(p: seq<bool>, h : nat) 
        requires |p| == h - 1 >= 1
        ensures bitListToNat(p) < power2(h - 1) / 2 ==> p[0] == false
    {   //  Thanks  
    }

    lemma foo35(p: seq<bool>, r : Tree)
        requires isCompleteTree(r)
        requires height(r) >= 2
        requires |p| >= 1
        requires |p| == height(r) - 1 
        ensures match r 
            case Node(_, lc, rc) =>
                (bitListToNat(p) < power2(height(r) - 1) / 2 ==> leafAt(p, r) in collectLeaves(lc))
                &&
                (bitListToNat(p) >= power2(height(r) - 1) / 2 ==> leafAt(p, r) in collectLeaves(rc))
    {

    }
     
} 
