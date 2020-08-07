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
     *  Make an indexed tree from a tree.
     *
     *  @param  r   The root of the tree.
     *  @param  p   The prefix to use in indexing.
     *  @returns    A indexed tree where each node has an index as
     *              a sequence of 0 (left) and 1 (right). The id of 
     *              corresponds to the path from the root. 
     */
    function toIndexed<T>(r : Tree<T>, p : seq<bit>) : ITree<T> 
        ensures {:induction r} forall n :: n in nodesIn(toIndexed(r, p)) ==> |n.id| >= |p| 
        ensures isValidIndex(toIndexed(r, p), p)
        decreases r
    {
        match r 
            case Leaf(v) => ILeaf(v, p)
            case Node(v, lc, rc) => 
                INode(v, toIndexed(lc, p + [0]), toIndexed(rc, p + [1]), p)
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
    function method leavesIn(root : ITree) : seq<ITree>
        /** All the collected nodes are leaves. */
        ensures forall i :: 0 <= i < |leavesIn(root)| ==>  leavesIn(root)[i].ILeaf?
        /** All the leaves are collected. */
        ensures forall n :: n in nodesIn(root) && n.ILeaf? ==> n in leavesIn(root)
        decreases root
    {
        match root 
            case ILeaf(_, _) => [ root ] 
            case INode(_, lc, rc, _) =>  
                leavesIn(lc) + leavesIn(rc) 
    }

    /**
     *  The node at the end of a path.
     *
     *  @param  p   A path (left/right) in a binary tree.
     *  @param  r   A complete binary tree.
     *
     *  @returns    The node of the tree that is the target of path `p`.
     */
    function nodeAt(p : seq<bit>, r: ITree) : ITree
        requires |p| < height(r) 
        requires isCompleteTree(r)
        ensures nodeAt(p, r) in nodesIn(r)
        decreases p
    {
        if |p| == 0 then  
            r
        else 
            // r must be a node as height(r) > |p| >= 1
            match r 
                case INode(_, lc, rc, _) => 
                    nodeAt(p[1..], if p[0] == 0 then lc else rc)
    }

    /**
     *  The siblings (left or roght) of each node (except root) on the path.
     */
    function siblingAt(p : seq<bit>, r :ITree) : ITree
        requires 1 <= |p| < height(r) 
        requires isCompleteTree(r)
        decreases p
    {
        if |p| == 1 then
            match r 
                case INode(_, lc, rc, _) =>
                    if p[0] == 0 then rc
                    else lc
        else 
            match r 
                case INode(_, lc, rc, _) => 
                    if p[0] == 0 then 
                        siblingAt(p[1..], lc)
                    else 
                        siblingAt(p[1..], rc)
    }

    //  Predicates 

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

    /**
     *  Check that a decorated tree correctly stores the f attribute. 
     */
    predicate isDecoratedWith<T>(f : (T, T) -> T, root: ITree<T>)
        decreases root
    {
        match root

            case ILeaf(v,_) => 
                    //  leaves define the attributes
                    true

            case INode(v, lc, rc, _) => 
                    //  Recursive definition for an internal node: children are
                    //  well decorated and node value if the f between children.
                    v == f(lc.v, rc.v)
                    && isDecoratedWith(f, lc)
                    && isDecoratedWith(f, rc)
    }

    /**
     *  The tree decorated with constant values.
     *  
     *  @param  r   A tree.
     *  @param  c   A value.
     *  @returns    True if and olny if all values are equal to `c`.
     */
    predicate isConstant<T>(r : ITree<T>, c: T) 
        decreases r
    {
        match r 
            case ILeaf(v,_) => v == c
            case INode(v, lc, rc,_) => v == c
                            && isConstant(lc, c) 
                            && isConstant(rc, c)
    }

    //  Properties of (indexed) trees.

    /**
     *  The node obtained after a path is the id of rhe node in 
     *  a validIndex tree.
     */
    lemma {:induction p} nodeIdAtPathIsPath(p : seq<bit>, p': seq<bit>, r: ITree) 
        requires |p| < height(r) 
        requires isCompleteTree(r)
        requires isValidIndex(r, p') 
        ensures nodeAt(p, r).id == p' + p
        decreases r
    {
        if |p| == 0 {
            //  Thanks Dafny
        } else {
            match r 
                case INode(_, lc, rc, id) =>
                    if p[0] == 0 {
                        //  nodeAt is in lc after p[1..]
                        nodeIdAtPathIsPath(p[1..], p' + [0], lc);
                        calc == {
                            nodeAt(p[1..], lc).id ;
                            == calc == {
                                nodeAt(p, r) ;
                                == 
                                nodeAt(p[1..], lc);
                            }
                            nodeAt(p[1..], lc).id;
                            ==
                            p' + [0] + p[1..];
                        }
                    } else {   
                         //  nodeAt is in rc after p[1..]
                        nodeIdAtPathIsPath(p[1..], p' + [1], rc);
                        calc == {
                            nodeAt(p[1..], rc).id ;
                            == calc == {
                                nodeAt(p, r) ;
                                == 
                                nodeAt(p[1..], rc);
                            }
                            nodeAt(p[1..], rc).id;
                            ==
                            p' + [1] + p[1..];
                        }
                    }
        }
    }

    // lemma leaveIdAtPathIsPath(p : seq<bit>, p': seq<bit>, r: ITree) 
    //     requires |p| == height(r) - 1 
    //     requires isCompleteTree(r)
    //     requires isValidIndex(r, p') 
    //     requires k < power2(height(r) - 1)
    //     ensures leaveIn(r)[k].id == p' + p
    //     decreases r
    // {}

    /**
     *  Index of each node of a indexed tree that is valid is >= `p`.
     */
    lemma {:induction t} toIndexedIsMonotonic(t : ITree, p : seq<bit>, n : nat)
        requires isValidIndex(t, p) 
        requires 0 <= n < |nodesIn(t)|
        /** Weak ordering for all nodes. */
        ensures p <= nodesIn(t)[n].id 
        /** For nodes in lc and rc, strict prefix ordering wrt root.id.. */
        ensures n >= 1 ==> p < nodesIn(t)[n].id 
        decreases t 
    {
        match t 
            case ILeaf(_, _) =>

            case INode(_, lc, rc, _) => 
                if ( n == 0 ) {
                    //  Thanks Dafny
                }  else if ( 1 <= n <= |nodesIn(lc)|) {
                    toIndexedIsMonotonic(lc, p + [0], n - 1);
                } else {
                    toIndexedIsMonotonic(rc, p + [1], n - 1 - |nodesIn(lc)|);
                }
    }

    /**
     *  Each node has a unique id in a validIndexed tree.
     */
    lemma {:induction r} eachNodeHasUniqueId(r: ITree, k1 : nat, k2 : nat, p : seq<bit>) 
        requires isValidIndex(r, p) 
        /** Two arbitrary strictly ordered indices within the range of nodesIn  */
        requires 0 <= k1 < k2 < |nodesIn(r)|
        /** The ids of two arbitary nodes are not equal. */
        ensures nodesIn(r)[k1].id !=  nodesIn(r)[k2].id
        decreases r
    { 
        match r 
            case ILeaf(v, id) => // Vacuously true. Thanks Dafny

            case INode(v, lc, rc, id) =>

                if ( k1 == 0 ) {
                    //  k2 is an index of a node in lc or rc, strict ordering applies.
                    toIndexedIsMonotonic(r, p, k2);
                } else if 1 <= k1 < k2 <= |nodesIn(lc)| {
                    //  both indices are nodes in lc. Use induction hypothesis on lc.
                    eachNodeHasUniqueId(lc, k1 - 1, k2 - 1, p + [0]);
                } else if 1 + |nodesIn(lc)| <= k1 < k2 < |nodesIn(r)| {
                    //  both indices are nodes in rc. Use induction hypothesis on rc. 
                    var i1 := k1 - 1 - |nodesIn(lc)|;
                    var i2 := k2 - 1 - |nodesIn(lc)|;
                    eachNodeHasUniqueId(rc, i1, i2, p + [1]);   
                } else {
                    //  k1 indexes a node in lc.
                    assert ( 1 <= k1 <= 1 + |nodesIn(lc)| <= k2 < |nodesIn(r)| );
                    var i1 := k1 - 1;
                    //  Use induction hypothesis on lc. ids on nodes in lc >= p + [0]
                    toIndexedIsMonotonic(lc, p + [0], i1);

                    //  k2 indexes a node in rc.
                    var i2 := k2 - 1 - |nodesIn(lc)|;
                    //  Use induction hypothesis on rc. Ids of nodes in rc >= p + [1]
                    toIndexedIsMonotonic(rc, p + [1], i2);

                    //  Prove post condition by contradiction. 
                    //  Idea: lc nodes start with p + [0] and rc nodes with p + [1].
                    //  Turns out that p + [0] + p' != p + [1] + p' for all p'.
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


    //  Helpers lemmas for complete trees.

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

    /**
     *  If the id of root is [], then each node n.id is the path
     *  from root to n.
     */
    lemma {:induction r} nodeAtCanonicalPath(p : seq<bit>, r : ITree) 
         requires |p| < height(r) 
        requires isCompleteTree(r)
        requires isValidIndex(r, [])
        ensures nodeAt(p, r).id == p 
    {
        nodeIdAtPathIsPath(p, [], r);
    } 

    // lemma {:induction r} foo201(r: ITree, p: seq<bit>, lc1: ITree) 
    //     requires height(r) >= 2
    //     requires isCompleteTree(r)
    //     requires isValidIndex(r, [])
    //     requires |p| == height(r) - 1
    //     requires isValidIndex(lc1, [])
    //     requires isCompleteTree(lc1)
    //     requires height(lc1) == height(r) - 1
    //     requires p[0] == 0 

    //     ensures match r     
    //         case INode(_, lc, rc, _) =>
    //             // if p[0] == 0 then
    //                 nodeAt(p[1..], lc).id == nodeAt(p[1..], lc1).id
    //                 // && nodeAt(p[1..], lc).id == p[1..]
    //             // else 
    //                 // nodeAt(p, r).id == nodeAt(p[1..], rc).id

    // {   //  Thanks Dafny
    //     match r     
    //         case INode(_, lc, rc, _) =>
    //                 assert(isValidIndex(lc, [0]));
    //                 nodeAtCanonicalPath(p[1..], lc);   
    // }

    lemma nodeLoc(r : ITree, p : seq<bit>) 
        requires 1 <= |p| == height(r) - 1
        requires isCompleteTree(r)

        ensures match r 
            case INode(_, lc, rc, _) =>
                p[0] == 0 ==> nodeAt(p, r) in leavesIn(lc)
                &&
                p[0] == 1 ==> nodeAt(p, r) in leavesIn(rc)

    lemma nodeLoc2(r : ITree, p : seq<bit>, k : nat) 
        requires 1 <= |p| == height(r) - 1
        requires isCompleteTree(r)
        // requires isValidIndex(r, p')
        requires k < power2(height(r) - 1)
        requires k < |leavesIn(r)|
        // requires nodeAt(p, r).id == leavesIn(r)[k].id
        // requires p' + p == leavesIn(r)[k].id
        requires nodeAt(p, r) == leavesIn(r)[k]

        ensures match r 
            case INode(_, lc, rc, _) =>
                (p[0] == 0 && k < power2(height(r) - 1)/2)
                ||
                (p[0] == 1 && k >= power2(height(r) - 1)/2)

    /**
     *  Split of sequences.
     */
    lemma splitSeq<T>(s: seq<T>, t: seq<T>, u : seq<T>)
        requires s == t + u
        ensures s[..|t|] == t
        ensures s[|t|..] == u
    {   //  Thanks Dafny 
    }

    lemma suffixPrefixMerge<T>(s : seq<T>, i : nat)
        requires 1 <= i < |s|
        ensures s[1..][..i] == s[1..i + 1]
    {} 

    //  Synthesised attibutes Helpers

    // function decoratePath(r: ITree, l : seq<bit>, )
}