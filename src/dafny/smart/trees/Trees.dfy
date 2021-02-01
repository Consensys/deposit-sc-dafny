/*
 * Copyright 2021 ConsenSys Software Inc.
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

include "../helpers/Helpers.dfy"
include "../seqofbits/SeqOfBits.dfy"

/**
 *  Provide tree decorated with attribute values.
 */
module Trees {

    import opened Helpers
    import opened SeqOfBits

    /** 
     *  Binary trees.
     *
     *  @tparam T   The type of values attached to the nodes.
     *  @param  v   The value associated with a node.
     */
    datatype Tree<T> = 
            Leaf(v: T, ghost index : nat)
        |   Node(v: T, left: Tree, right: Tree)

    /**
     *  Height of a tree. Length of longest path from root to a leaf.
     *
     *  @param  root    The root of the tree.
     *  @returns        The height of the tree.
     */
    function height(root : Tree) : nat 
        ensures height(root) >= 0   //  not needed as result is of type nat.
        decreases root
    {
        match root 
            case Leaf(_, _) => 0

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
        ensures |nodesIn(root)| >= 1
        ensures nodesIn(root)[0] == root  
        decreases root
    {
        match root 
            case Leaf(_, _) => [ root ] 

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
            case Leaf(_,_) => [ root ] 

            case Node(_, lc, rc) =>  leavesIn(lc) + leavesIn(rc) 
    }

    //  Predicates on Trees.

    /**
     *  Check that a decorated tree correctly stores the synthesised attribute f. 
     *
     *  @param  f       The function to compute the attribute on a node
     *                  given the values on the children.
     *  @param  root    The root that defines the tree.
     *
     *  @note           We assume that the synthesised attribute is given
     *                  on the leaves and is not computed on them, so
     *                  a leaf is by definition well-decorated.
     */
    predicate isDecoratedWith<T>(f : (T, T) -> T, root: Tree<T>)
        decreases root
    {
        match root
            case Leaf(_, _) => true

            case Node(v, lc, rc) => 
                //  Recursive definition for an internal node: children 
                //  are well decorated and node's value is f applied to children.
                v == f(lc.v, rc.v) && isDecoratedWith(f, lc) && isDecoratedWith(f, rc)
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
            case Leaf(v,_) => v == c

            case Node(v, lc, rc) => v == c && isConstant(lc, c) && isConstant(rc, c)
    }

     /**
     *  Whether a tree is properly indexed (lexicographic order)
     *  from an initial value `p`.   
     *  
     *  @param  r   The root of the tree.
     *  @param  p   The prefix used for the id. 
     */
    predicate hasLeavesIndexedFrom(r: Tree, i : nat) 
    {
        forall k :: 0 <= k < |leavesIn(r)|  ==> leavesIn(r)[k].index == k + i
    }

    //  Constant tree iff same values on all nodes (and leaves)

    lemma {:induction r} isConstantImpliesSameValuesEveryWhere<T>(r : Tree<T>, c: T)
        requires isConstant(r, c)
        ensures  
            (forall k :: 0 <= k < |nodesIn(r)|  ==> nodesIn(r)[k].v == c)
            && (forall k :: 0 <= k < |leavesIn(r)|  ==> leavesIn(r)[k].v == c)
    {
        //  Thanks Dafny
    }

    //  Lemmas on trees.

    lemma {:induction r} sameValuesEveryWhereImpliesIsConstant<T>(r : Tree<T>, c: T)
        requires forall k :: 0 <= k < |nodesIn(r)|  ==> nodesIn(r)[k].v == c
        ensures isConstant(r, c) 
        decreases r 
    {
        if (height(r) == 0) {
            //  In this case, there is only one node.
            assert(nodesIn(r)[0] == r);
        } else {
            match r 
                case Node(v, lc, rc) =>
                    assert(nodesIn(r) == [r] + nodesIn(lc) + nodesIn(rc));
                    assert(nodesIn(lc)  == nodesIn(r)[1..|nodesIn(lc)| + 1]);
                    assert(nodesIn(rc)  == nodesIn(r)[|nodesIn(lc)| + 1..|nodesIn(r)|]);

                    //  Induction on lc and rc
                    sameValuesEveryWhereImpliesIsConstant(lc, c);
                    sameValuesEveryWhereImpliesIsConstant(rc, c);
                    
                    //  True for root.
                    assert(nodesIn(r)[0] == r);
        }
    }    
}