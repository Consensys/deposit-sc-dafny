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
include "SeqOfBits.dfy"
include "SeqHelpers.dfy"

/**
 *  Provide tree decorated with value and indexed trees.
 */
module Trees {

    import opened Helpers
    import opened SeqOfBits
    import opened SeqHelpers 

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
     *  Height of a tree.
     *
     *  @param  root    The root of the tree.
     *  @returns        The height of the tree.
     */
    function height(root : Tree) : nat 
        ensures height(root) >= 1
        decreases root
    {
        match root 
            case Leaf(_) => 1
            case Node(_, lc, rc) => 1 + max(height(lc), height(rc))
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
    function method nodesIn(root : Tree) : seq<Tree>
        decreases root
    {
        match root 
            case Leaf(_) => [ root ] 
            case Node(_, lc, rc) =>  [ root ] + nodesIn(lc) + nodesIn(rc) 
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
    function method leavesIn(root : Tree) : seq<Tree>
        /** All the collected nodes are leaves. */
        ensures forall i :: 0 <= i < |leavesIn(root)| ==>  leavesIn(root)[i].Leaf?
        /** All the leaves are collected. */
        ensures forall n :: n in nodesIn(root) && n.Leaf? ==> n in leavesIn(root)
        decreases root
    {
        match root 
            case Leaf(_) => [ root ] 
            case Node(_, lc, rc) =>  
                leavesIn(lc) + leavesIn(rc) 
    }

    
    //  Predicates 

    /**
     *  Check that a decorated tree correctly stores the f attribute. 
     */
    predicate isDecoratedWith<T>(f : (T, T) -> T, root: Tree<T>)
        decreases root
    {
        match root

            case Leaf(v) => 
                    //  leaves define the attributes
                    true

            case Node(v, lc, rc) => 
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
    predicate isConstant<T>(r : Tree<T>, c: T) 
        decreases r
    {
        match r 
            case Leaf(v) => v == c
            case Node(v, lc, rc) => v == c
                            && isConstant(lc, c) 
                            && isConstant(rc, c)
    }
}