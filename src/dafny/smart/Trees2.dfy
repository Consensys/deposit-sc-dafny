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
 *  Provide tree decorated with attribute values.
 */
module Trees {

    import opened Helpers

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
     *  @return         The sequence of nodes (including leaves) that corresponds to 
     *                  the pre-order (node, left, right) traversal of a tree.
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
     */
    function method leavesIn(root : Tree) : seq<Tree>
        /** Sanity check: All the collected nodes are leaves. */
        ensures forall i :: 0 <= i < |leavesIn(root)| ==>  leavesIn(root)[i].Leaf?
        /** All the leaves are collected. */
        ensures forall n :: n in nodesIn(root) && n.Leaf? ==> n in leavesIn(root)
        ensures forall n :: n in leavesIn(root) ==> n in nodesIn(root) && n.Leaf? 
        decreases root
    {
        match root 
            case Leaf(_) => [ root ] 
            case Node(_, lc, rc) =>  
                leavesIn(lc) + leavesIn(rc) 
    }

    //  Predicates on Trees.

    /**
     *  Check that a decorated tree correctly stores the synthesised attribute f. 
     *
     *  @param  t       The function to compute the attribute on a node
     *                  given the values on the children.
     *  @param  root    The root that defines the tree.
     *
     *  @note           We assume that the synthesised attribute is given
     *                  on the leaves and is not computed on them. 
     */
    predicate isDecoratedWith<T>(f : (T, T) -> T, root: Tree<T>)
        decreases root
    {
        match root
            case Leaf(v) => true

            case Node(v, lc, rc) => 
                    //  Recursive definition for an internal node: children 
                    //  are well decorated and node's value is f applied to children.
                    v == f(lc.v, rc.v)
                    && isDecoratedWith(f, lc)
                    && isDecoratedWith(f, rc)
    }

    /**
     *  Check that a tree is decorated with a single value.
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