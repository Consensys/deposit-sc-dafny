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
 *  Provide tree decorated with value and indexed trees.
 */
module Trees {

    import opened Helpers

    newtype{:nativeType "int"} bit = i:int | 0 <= i < 2

    /** 
     *  Binary trees.
     *
     *  @tparam T   The type of values attached to the nodes.
     *  @param  v   The value associated with a node.
     */
    datatype Tree<T> = 
            Leaf(v: T)
        |   Node(v: T, left: Tree, right: Tree)

    /** 
     *  Binary trees with node identifier.
     *  
     *  @tparam T   The type of values attached to the nodes.
     *  @param  v   The value associated with a node.
     *  @param  id  A sequence that corresponds to the node id.
     */
    datatype ITree<T> = 
            ILeaf(v: T, ghost id: seq<bit>)
        |   INode(v: T, left: ITree, right: ITree, ghost id : seq<bit>)

    /**
     *  Height of a tree.
     *
     *  @param  root    The root of the tree.
     *  @returns        The height of the tree.
     */
    function height(root : ITree) : nat 
        ensures height(root) >= 1
        decreases root
    {
        match root 
            case ILeaf(_, _) => 1
            case INode(_, lc, rc, _) => 1 + max(height(lc), height(rc))
    }

    /**
     *  Whether a tree is properly indexed (lexicographic order)
     *  from an initial value `p`.   
     *  
     *  @param  r   The root of the tree.
     *  @param  p   The prefix used for the id. 
     */
    predicate isValidIndex(r: ITree, p : seq<bit>) 
        decreases r
    {
       match r 
            case ILeaf(_, id) => id == p

            case INode(_, lc, rc, id) =>
                id == p && isValidIndex(lc, p + [0]) && isValidIndex(rc, p + [1]) 
    }

    /**
     *  Make an indexed tree from a tree.
     *
     *  @param  r   The root of the tree.
     *  @param  p   The prefix to use in indexing.
     *  @returns    A indexed tree where each node has an index as
     *              a sequence of 0 (left) and 1 (right). The id of 
     *              corresponds to the path from the root. 
     */
    function indexFrom<T>(r : Tree<T>, p : seq<bit>) : ITree<T> 
        ensures {:induction r} forall n :: n in nodesIn(indexFrom(r, p)) ==> |n.id| >= |p| 
        ensures isValidIndex(indexFrom(r, p), p)
        decreases r
    {
        match r 
            case Leaf(v) => ILeaf(v, p)
            case Node(v, lc, rc) => 
                INode(v, indexFrom(lc, p + [0]), indexFrom(rc, p + [1]), p)
    }

    

    // lemma foo32(r : ITree, p : seq<bit>) 
    //     requires isValidIndex(r, p) 
    //     ensures p <= r.id 
    // {}

    /**
     *  Index from an intial value 
     */
    // lemma {:induction r} indexFromMonotonic(r : Tree, t : ITree, p : seq<bit>, n : nat)
    //     requires t == indexFrom(r, p)
    //     requires 0 <= n < |nodesIn(t)|
    //     ensures p <= nodesIn(t)[n]. id 
    //     decreases r 
    // {
    //     match r 
    //         case Leaf(_) =>

    //         case Node(_, lc, rc) => 
    //             assert(t.INode?);
    //             match t 
    //                 case INode(_, tlc, trc, id) =>
    //                     assert(nodesIn(t) == [t] + nodesIn(tlc) + nodesIn(trc));
    //                     if ( n == 0 ) {
    //                         //  Thanks Dafny
    //                     }  else if ( 1 <= n <= |nodesIn(tlc)|) {
    //                         indexFromMonotonic(lc, tlc, p + [0], n - 1);
    //                     } else {
    //                         indexFromMonotonic(rc, trc, p + [1], n - 1 - |nodesIn(tlc)|);
    //                     }
    // }

    /**
     *  Index of each node of a indexed that is valid is >= `p`.
     */
    lemma {:induction t} indexFromMonotonic2(t : ITree, p : seq<bit>, n : nat)
        requires isValidIndex(t, p) 
        requires 0 <= n < |nodesIn(t)|
        ensures p <= nodesIn(t)[n].id 
        decreases t 
    {
        match t 
            case ILeaf(_, _) =>

            case INode(_, lc, rc, _) => 
                if ( n == 0 ) {
                    //  Thanks Dafny
                }  else if ( 1 <= n <= |nodesIn(lc)|) {
                    indexFromMonotonic2(lc, p + [0], n - 1);
                } else {
                    indexFromMonotonic2(rc, p + [1], n - 1 - |nodesIn(lc)|);
                }
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
    function method nodesIn(root : ITree) : seq<ITree>
        decreases root
    {
        match root 
            case ILeaf(_, _) => [ root ] 
            case INode(_, lc, rc, _) =>  [ root ] + nodesIn(lc) + nodesIn(rc) 
    }

    //  Property of indexed trees

    /**
     *  A nice lemma with a tedious proof.
     *  In a tree obtained with `indexFrom` each node has a unique id.
     */
    lemma {:induction t} uniqueNodeId(t: Tree, r: ITree, k1 : nat, k2 : nat, p : seq<bit>) 
        requires r == indexFrom(t, p)
        requires 0 <= k1 < k2 < |nodesIn(r)|
        ensures nodesIn(r)[k1].id != nodesIn(r)[k2].id
        decreases r
    {
        match r 
            case ILeaf(v, id) => // Vacuously true. Thanks Dafny

            case INode(v, lc, rc, id) =>

                // assert( nodesIn(r) == [r] + nodesIn(lc) + nodesIn(rc));
                if ( k1 == 0 ) {
                    //  ids in lc and rc have length r.id + 1
                    assert(p < nodesIn(r)[k2].id);
                } else if 1 <= k1 < k2 <= |nodesIn(lc)| {
                    //  both indices are nodes in lc
                    assert(0 <= k1 - 1 < k2 - 1 < |nodesIn(lc)|);
                    assert(t.Node?);
                    match t 
                        case Node(_, tlc, _) => 
                            assert(lc == indexFrom(tlc, p + [0]));
                            uniqueNodeId(tlc, lc, k1 - 1, k2 - 1, p + [0]);
                } else if 1 + |nodesIn(lc)| <= k1 < k2 < |nodesIn(r)| {
                    //  both indices are nodes in rc
                    var i1 := k1 - 1 - |nodesIn(lc)|;
                    var i2 := k2 - 1 - |nodesIn(lc)|;
                    assert(0 <= i1 < i2 < |nodesIn(rc)|);
                    assert(t.Node?);
                    match t 
                        case Node(_, _, trc) => 
                            assert(rc == indexFrom(trc, p + [1]));
                            uniqueNodeId(trc, rc, i1, i2, p + [1]);
                } else {
                    //  k1 indexed a node in lc and k2 a node in rc
                    assert ( 1 <= k1 < 1 + |nodesIn(lc)| <= k2 < |nodesIn(r)| );
                    assert(t.Node?);
                    match t 
                        case Node(_, tlc, trc) =>
                            assert(lc == indexFrom(tlc, p + [0]));
                            var i1 := k1 - 1;
                            indexFromMonotonic(tlc, lc, p + [0], i1);

                            assert(rc == indexFrom(trc, p + [1]));
                            var i2 := k2 - 1 - |nodesIn(lc)|;
                            indexFromMonotonic(trc, rc, p + [1], i2);

                            assert(p + [0] <= nodesIn(r)[k1].id );
                            assert(p + [1] <= nodesIn(r)[k2].id );

                            //  Prove post condition by contradiction
                            calc ==> {
                                nodesIn(r)[k1].id == nodesIn(r)[k2].id ;
                                ==>
                                nodesIn(r)[k1].id[..|p| + 1] == nodesIn(r)[k2].id[..|p| + 1] ;
                                ==> calc == {
                                        p + [0] ;
                                        ==
                                        (p + [0])[..|p| + 1];
                                        == 
                                        nodesIn(r)[k1].id[..|p| + 1];
                                }
                                p + [0] == nodesIn(r)[k2].id[..|p| + 1] ;
                                ==> calc == {
                                        p + [1] ;
                                        ==
                                        (p + [1])[..|p| + 1];
                                        == 
                                        nodesIn(r)[k2].id[..|p| + 1];
                                }
                                p + [0] == p + [1];
                                ==>
                                (p + [0])[|p|] == (p + [1])[|p|];
                                ==>
                                //  contradiction
                                0 == 1;
                            }
                }
    }

    lemma {:induction r} uniqueNodeId2(r: ITree, k1 : nat, k2 : nat, p : seq<bit>) 
        requires isValidIndex(r, p) 
        requires 0 <= k1 < k2 < |nodesIn(r)|
        ensures nodesIn(r)[k1].id != nodesIn(r)[k2].id
        decreases r
    {
        match r 
            case ILeaf(v, id) => // Vacuously true. Thanks Dafny

            case INode(v, lc, rc, id) =>

                // assert( nodesIn(r) == [r] + nodesIn(lc) + nodesIn(rc));
                if ( k1 == 0 ) {
                    //  ids in lc and rc have length r.id + 1
                    assert(p < nodesIn(r)[k2].id);
                } else if 1 <= k1 < k2 <= |nodesIn(lc)| {
                    //  both indices are nodes in lc
                    assert(0 <= k1 - 1 < k2 - 1 < |nodesIn(lc)|);
                    // assert(t.Node?);
                    // match t 
                    //     case Node(_, tlc, _) => 
                    //         assert(lc == indexFrom(tlc, p + [0]));
                    uniqueNodeId2(lc, k1 - 1, k2 - 1, p + [0]);
                } else if 1 + |nodesIn(lc)| <= k1 < k2 < |nodesIn(r)| {
                    //  both indices are nodes in rc
                    var i1 := k1 - 1 - |nodesIn(lc)|;
                    var i2 := k2 - 1 - |nodesIn(lc)|;
                    assert(0 <= i1 < i2 < |nodesIn(rc)|);
                    // assert(t.Node?);
                    // match t 
                    //     case Node(_, _, trc) => 
                    //         assert(rc == indexFrom(trc, p + [1]));
                    uniqueNodeId2(rc, i1, i2, p + [1]);
                } else {
                    //  k1 indexed a node in lc and k2 a node in rc
                    assert ( 1 <= k1 < 1 + |nodesIn(lc)| <= k2 < |nodesIn(r)| );
                    // assert(t.Node?);
                    // match t 
                        // case Node(_, tlc, trc) =>
                        //     assert(lc == indexFrom(tlc, p + [0]));
                        var i1 := k1 - 1;
                        indexFromMonotonic2(lc, p + [0], i1);

                        // assert(rc == indexFrom(trc, p + [1]));
                        var i2 := k2 - 1 - |nodesIn(lc)|;
                        indexFromMonotonic2(rc, p + [1], i2);

                        assert(p + [0] <= nodesIn(r)[k1].id );
                        assert(p + [1] <= nodesIn(r)[k2].id );

                        //  Prove post condition by contradiction
                        calc ==> {
                            nodesIn(r)[k1].id == nodesIn(r)[k2].id ;
                            ==>
                            nodesIn(r)[k1].id[..|p| + 1] == nodesIn(r)[k2].id[..|p| + 1] ;
                            ==> calc == {
                                    p + [0] ;
                                    ==
                                    (p + [0])[..|p| + 1];
                                    == 
                                    nodesIn(r)[k1].id[..|p| + 1];
                            }
                            p + [0] == nodesIn(r)[k2].id[..|p| + 1] ;
                            ==> calc == {
                                    p + [1] ;
                                    ==
                                    (p + [1])[..|p| + 1];
                                    == 
                                    nodesIn(r)[k2].id[..|p| + 1];
                            }
                            p + [0] == p + [1];
                            ==>
                            (p + [0])[|p|] == (p + [1])[|p|];
                            ==>
                            //  contradiction
                            0 == 1;
                        }
                }
    }
    
    /**
     *  The node at the end of a path.
     *
     *  @param  p   A path (left/right) in a binary tree.
     *  @param  r   A complete binary tree.
     *
     *  @returns    The node of the tree that is the target of path `p`.
     */
    // function nodeAt(p : seq<bit>, r: Tree) : Tree
    //     requires |p| < height(r) 
    //     requires isCompleteTree(r)
    //     ensures nodeAt(p, r) in collectNodes(r)
    //     decreases p
    // {
    //     if |p| == 0 then  
    //         r
    //     else 
    //         // r must be a node as height(r) > |p| >= 1
    //         match r 
    //             case Node(_, lc, rc, _) => 
    //                 nodeAt(p[1..], if p[0] == 0 then lc else rc)
    // }

    /**
     *  Collect nodes on the right hand-side of a full path.
     *  
     *  @param  p   A path.
     *  @param  r   A complete binary tree.
     */
    // function nodesRightOf(p: seq<bit>, r : Tree) : seq<Tree> 
    //     requires |p| == height(r) - 1 
    //     requires isCompleteTree(r)
    //     decreases p
    // {
    //     if |p| == 0 then
    //         []
    //     else
    //         match r 
    //             case Node(_, lc, rc, _) =>
    //                 if p[0] == 0 then
    //                     collectNodes(rc) + nodesRightOf(p[1..], lc)
    //                 else 
    //                     nodesRightOf(p[1..], rc)
    // }

    /**
     *  The node at a depth height(r) - 1 is a leaf.
     */
    // lemma {:induction p, r} nodeAfterFullPathIsLeaf(p : seq<bit>, r : Tree) 
    //     requires |p| == height(r) - 1 
    //     requires isCompleteTree(r)
    //     ensures nodeAt(p, r).Leaf?
    // {   //  Thanks Dafny
    // }

    /**
     *  The leaf that corresponds to a path of length height(r) - 1.
     *
     *  @param  p   A full path.
     *  @param  t   A complete binary tree.
     *  @returns    The leaf at the end of the path.
     */
    // function leafAt(p : seq<bit>, r: Tree) : Tree
    //     requires |p| == height(r) - 1 
    //     requires isCompleteTree(r)
    //     ensures leafAt(p, r).Leaf?
    //     ensures leafAt(p, r) in collectLeaves(r)
    // {
    //     //  Proof of post-condition
    //     nodeAfterFullPathIsLeaf(p, r);
    //     nodeAt(p, r)
    // }

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
    // function leftRight(p : seq<bit>, r: Tree) : seq<Tree>
    //     requires |p| == height(r) - 1
    //     requires isCompleteTree(r)
    //     ensures |leftRight(p, r)| == |p|
    //     decreases p
    // {
    //     match r 
    //         case Leaf(_, _) => []

    //         case Node(_, lc, rc, _) => 
    //             if p[0] == 0 then
    //                 [lc] + leftRight(p[1..], lc)
    //             else 
    //                 [rc] + leftRight(p[1..], rc)
    // }

    

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
    // function method collectLeaves(root : Tree) : seq<Tree>
    //     /** All the collected nodes are leaves. */
    //     ensures forall i :: 0 <= i < |collectLeaves(root)| ==>  collectLeaves(root)[i].Leaf?
    //     /** All the leaves are collected. */
    //     ensures forall n :: n in collectNodes(root) && n.Leaf? ==> n in collectLeaves(root)
    //     decreases root
    // {
    //     match root 
    //         case Leaf(_, _) => [ root ] 
    //         case Node(_, lc, rc, _) =>  
    //             collectLeaves(lc) + collectLeaves(rc) 
    // }
    
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

    //  Helpers lemmas.

    /**
     *  Relation between height and number of leaves in a complete tree.
     */
    // lemma {:induction root} completeTreeNumberOfLeaves(root : Tree) 
    //     ensures isCompleteTree(root) ==> |collectLeaves(root)| == power2(height(root) - 1)
    // {   //  Thanks Dafny
    // }

    /**
     *  Relation between height and number of nodes in a complete tree.
     */
    // lemma {:induction root} completeTreeNumberOfNodes(root : Tree) 
    //     ensures isCompleteTree(root) ==> |collectNodes(root)| == power2(height(root)) - 1
    // {   //  Thanks Dafny
    // }

    /**
     *  Two complete tree of same height have same number of leaves.
     */
    // lemma {:induction r1, r2} completeTreesOfSameHeightHaveSameNumberOfLeaves(r1: Tree, r2: Tree) 
    //     requires isCompleteTree(r1)
    //     requires isCompleteTree(r2)
    //     ensures height(r1) == height(r2) ==> |collectLeaves(r1)| == |collectLeaves(r2)|
    // {   //  Thanks Dafny
    // }

    /**
     *  Children of a node in a complete tree have same number of leaves.
     */
    // lemma {:induction r} completeTreesLeftRightHaveSameNumberOfLeaves(r : Tree) 
    //     requires isCompleteTree(r)
    //     requires height(r) >= 2
    //     ensures match r
    //         case Node(_, lc, rc, _) => 
    //             |collectLeaves(lc)| == |collectLeaves(rc)| == power2(height(r) - 1) / 2
    // {
    //     match r 
    //         case Node(_, lc, rc, _) =>
    //             completeTreesOfSameHeightHaveSameNumberOfLeaves(lc,rc);
    // }

    /**
     *  Split of sequences.
     */
    // lemma splitSeq<T>(s: seq<T>, t: seq<T>, u : seq<T>)
    //     requires s == t + u
    //     ensures s[..|t|] == t
    //     ensures s[|t|..] == u
    // {   //  Thanks Dafny
    // }
}