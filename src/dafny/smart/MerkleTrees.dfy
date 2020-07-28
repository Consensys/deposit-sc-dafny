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
include "Trees.dfy"

module MerkleTrees {

    import opened Helpers
    import opened Trees
 
    /**
     *  
     *  @param  l       A list of elements.
     *  @param  root    A tree.
     *  @param  default The default vakue for right-padding the tree leaves.
     *
     *  We assume collectLeaves return an indexed from left to right list of leaves.
     *
     *  @todo           We can use another function that returns the values instead
     *                  of collectleaves (returns the seq of values directly) and then
     *                  no need for `x.v`.
     */
    predicate treeLeftmostLeavesMatchList<T>(l: seq<T>, root: Tree<T>, default: T)
        requires |l| <= |collectLeaves(root)|
    {
        forall i:: 
            (0 <= i < |l| ==> l[i] == collectLeaves(root)[i].v)
            && 
            (|l| <= i < |collectLeaves(root)|  ==> collectLeaves(root)[i].v == default)
    }

    /**
     *  Default value for a given type.
     */
    // function default<T>() : T 

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
    *  Defines the Tree associated with a given sequence.
    *  
    *  @note   T   his function does not compute the tree but rather
    *              defines its properties: correctly stores the attribute
    *              `diff` and the leftmost |l| leaves store l.
    *
    *   @param  l   A list of values.
    *   @param  h   A height.
    *   @param  f   A function to combine two values.
    *   @param  d   A default value for the leaves not in `l`.
    */
    function buildMerkle<T>(l: seq<T>, h : nat, f : (T, T) -> T, d : T) : Tree<T> 
        requires h >= 1
        /** Tree has enough leaves to store `l`. */
        requires |l| <= power2(h - 1)      

        ensures height(buildMerkle(l, h, f, d)) == h
        ensures isCompleteTree(buildMerkle(l, h, f, d))
        ensures |collectLeaves(buildMerkle(l, h, f, d))| == power2(h - 1)
        ensures isDecoratedWith(f, buildMerkle(l, h, f, d))
        ensures treeLeftmostLeavesMatchList(l, buildMerkle(l, h, f, d), d)

        /**
         *  The tree decorated with constant values.
         *  
         *  @param  r   A tree.
         *  @param  c   A value.
         *  @returns    True if and olny if all values are equal to `c`.
         */
        predicate isConstantTree<T>(r : Tree<T>, c: T) 
            decreases r
        {
            match r 
                case Leaf(v) => v == c
                case Node(v, lc, rc) => v == c
                                && isConstantTree(lc, c) 
                                && isConstantTree(rc, c)
        }

    //  Helpers lemmas


}
