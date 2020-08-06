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
include "Trees2.dfy"

module MerkleTrees {

    import opened Helpers
    import opened Trees
 
    /**
     *  
     *  @param  l       A list of elements.
     *  @param  root    A tree.
     *  @param  default The default vakue for right-padding the tree leaves.
     *
     *  We assume leavesIn return an indexed from left to right list of leaves.
     *
     *  @todo           We can use another function that returns the values instead
     *                  of collectleaves (returns the seq of values directly) and then
     *                  no need for `x.v`.
     */
    predicate treeLeftmostLeavesMatchList<T>(l: seq<T>, root: ITree<T>, default: T)
        requires |l| <= |leavesIn(root)|
    {
        forall i:: 
            (0 <= i < |l| ==> l[i] == leavesIn(root)[i].v)
            && 
            (|l| <= i < |leavesIn(root)|  ==> leavesIn(root)[i].v == default)
    }

    /**
     *  Whether the tree is a Merkle Tree.
     *
     *  The tree must be:
     *      1.  complete
     *      2.  the first |l| leftmost leaves hold the values of `l`
     *      3.  the values on the internal nodes correspond to the value of
     *          synthesied attribute `f`.
     */
    predicate isMerkle<T>(root: ITree<T>, l: seq<T>, f : (T, T) -> T, default: T) 
        requires |l| <= |leavesIn(root)|
    {
        isCompleteTree(root)
        && isDecoratedWith(f, root)
        && treeLeftmostLeavesMatchList(l, root, default)
    }

    /**
     *  Whether the tree is a Merkle Tree for a given list of elements.
     *
     *  The tree must be:
     *      1.  complete
     *      2.  the values on the internal nodes correspond to the value of
     *          synthesised attribute `f`.
     *      3.  the leaves (in-order) hold the values of `l`
     *     
     */
    predicate isMerkle2<T>(root: ITree<T>, l: seq<T>, f : (T, T) -> T) 
        requires |l| == |leavesIn(root)|
    {
        isCompleteTree(root)                                            //  1.
        && isDecoratedWith(f, root)                                     //  2.
        && forall i :: 0 <= i < |l| ==> l[i] == leavesIn(root)[i].v     //  3.
           
    }

    lemma {:induction h} isMerkleChildren<T>(r: ITree<T>, l: seq<T>, f : (T, T) -> T, default: T, h : nat)
        requires |l| == |leavesIn(r)| / 2
        requires isMerkle(r, l, f, default)
        requires h == height(r) >= 2
        ensures match r 
            case INode(_, lc, rc, _) =>
                |leavesIn(lc)| == power2(height(r) - 1)/2
                && |l| <=  |leavesIn(lc)|
                && isMerkle(lc, l, f, default)
    {
        if h == 2 {
            //  Thanks Dafny
        } else {
            completeTreesLeftRightChildrenLeaves(r, h);
        }
    }

    /**
     *  For tree of height >= 2, Merkle projects onto lc and rc for 
     *  split list. 
     */
    lemma {:induction h} isMerkleChildren2<T>(r: ITree<T>, l: seq<T>, f : (T, T) -> T, h : nat)
        requires |l| == |leavesIn(r)|
        requires isMerkle2(r, l, f)
        requires h == height(r) >= 2
        ensures |l| == power2(height(r) - 1)
        ensures match r 
            case INode(_, lc, rc, _) =>
                |leavesIn(lc)| == power2(height(r) - 1)/2
                && |l[.. power2(height(r) - 1)/2]| <=  |leavesIn(lc)|
                && isMerkle2(lc, l[..  power2(height(r) - 1)/2], f)
                && |leavesIn(rc)| == power2(height(r) - 1)/2
                && |l[power2(height(r) - 1)/2..]| <=  |leavesIn(rc)|
                && isMerkle2(rc, l[power2(height(r) - 1)/2..], f)
    {
        if h == 2 {
            //  Thanks Dafny
        } else {
            completeTreesLeftRightChildrenLeaves(r, h);
        }
    }

    /**
     *  Default value for a given type.
     */
    // function default<T>() : T 

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
    function buildMerkle<T>(l: seq<T>, h : nat, f : (T, T) -> T, d : T) : ITree<T> 
        requires h >= 1
        /** Tree has enough leaves to store `l`. */
        requires |l| <= power2(h - 1)      

        ensures height(buildMerkle(l, h, f, d)) == h
        ensures isCompleteTree(buildMerkle(l, h, f, d))
        ensures |leavesIn(buildMerkle(l, h, f, d))| == power2(h - 1)
        ensures isDecoratedWith(f, buildMerkle(l, h, f, d))
        ensures treeLeftmostLeavesMatchList(l, buildMerkle(l, h, f, d), d)

    //  Helpers lemmas

    

}
