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

include "helpers/Helpers.dfy"
include "trees/Trees.dfy"
include "trees/CompleteTrees.dfy"
include "paths/PathInCompleteTrees.dfy"
include "synthattribute/RightSiblings.dfy"
include "seqofbits/SeqOfBits.dfy"


module MerkleTrees {

    import opened Helpers
    import opened Trees
    import opened CompleteTrees
    import opened PathInCompleteTrees
    import opened RSiblings
    import opened SeqOfBits

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
    predicate treeLeftmostLeavesMatchList<T>(l: seq<T>, root: Tree<T>, default: T)
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
    predicate isMerkle<T>(root: Tree<T>, l: seq<T>, f : (T, T) -> T, default: T) 
        requires |l| <= |leavesIn(root)| || |l| <= power2(height(root))
    {
        isCompleteTree(root)
        && |leavesIn(root)| == power2(height(root))
        && isDecoratedWith(f, root)
        && treeLeftmostLeavesMatchList(l, root, default)
    }

    /**
     *  Whether the tree is a Merkle Tree for a given list of elements.
     *  
     *  @param  root    A complete tree.
     *  @param  l       A list of values.
     *  @param  f       A binary operation.
     *  @returns        True if and only if the tree is decorated with f
     *                  and the leaves's values agree with `l`.
     *
     *  The tree must be:
     *      1.  complete
     *      2.  the values on the internal nodes correspond to the value of
     *          synthesised attribute `f`.
     *      3.  the leaves (in-order) hold the values of `l`
     *
     *  @todo   Change the name at some point as Merkle is used for hash attribute.
     */
    predicate isMerkle2<T>(root: Tree<T>, l: seq<T>, f : (T, T) -> T) 
        requires |l| == |leavesIn(root)|
    {
        isCompleteTree(root)
        && isDecoratedWith(f, root)                                     
        && forall i :: 0 <= i < |l| ==> l[i] == leavesIn(root)[i].v                
    }

    /**
     *  For tree of height >= 1, Merkle projects onto lc and rc for 
     *  split list. 
     *  @param  root    A complete tree.
     *  @param  l       A list of values.
     *  @param  f       A binary operation.
     *  @param  h       The height of the tree.
     *  @returns        True if and only if the tree is decorated with f
     *                  and the leaves's values agree with `l`.
     *
     */
    lemma {:induction h} treeIsMerkleImpliesChildrenAreMerkle<T>(r: Tree<T>, l: seq<T>, f : (T, T) -> T, h : nat)
        requires |l| == |leavesIn(r)|
        requires isMerkle2(r, l, f)
        requires h == height(r) >= 1
        ensures |l| == power2(height(r) )
        ensures match r 
            case Node(_, lc, rc) =>
                |leavesIn(lc)| == power2(height(r))/2
                && |l[.. power2(height(r))/2]| <=  |leavesIn(lc)|
                && isMerkle2(lc, l[..  power2(height(r))/2], f)
                && |leavesIn(rc)| == power2(height(r))/2
                && |l[power2(height(r))/2..]| <=  |leavesIn(rc)|
                && isMerkle2(rc, l[power2(height(r))/2..], f)
    {
        reveal_power2();
        childrenInCompTreesHaveHalfNumberOfLeaves(r, h);
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
    function {:axiom} buildMerkle<T>(l: seq<T>, h : nat, f : (T, T) -> T, d : T) : Tree<T> 
        requires h >= 0
        /** Tree has enough leaves to store `l`. */
        requires |l| <= power2(h)      

        ensures height(buildMerkle(l, h, f, d)) == h
        ensures isCompleteTree(buildMerkle(l, h, f, d))
        ensures |leavesIn(buildMerkle(l, h, f, d))| == power2(h)
        ensures isDecoratedWith(f, buildMerkle(l, h, f, d))
        ensures treeLeftmostLeavesMatchList(l, buildMerkle(l, h, f, d), d)
        ensures hasLeavesIndexedFrom(buildMerkle(l, h, f, d), 0)


    /**
     *  The right siblings of the path to the last element of the list are
     *  zeroes.  
     *
     *  @param  l   A list of values.
     *  @param  r   A merkle tree for l.
     *  @param  f   A function to combine values.
     *  @param  d   A default value for the leaves not in `l`.
     */
    lemma pathToLastInMerkleTreeHasZeroRightSiblings<T>(l: seq<T>, r: Tree<T>, f : (T, T) -> T, d : T) 
        requires hasLeavesIndexedFrom(r, 0) 
        requires height(r) >= 1
        /** The list has at least one element. */
        requires 1 <= |l| < power2(height(r))
        requires isMerkle(r, l, f, d)

        ensures var p := natToBitList(|l| - 1, height(r));
            forall i :: 0 <= i < |p| && p[i] == 0 ==> 
                siblingValueAt(p, r, i + 1) == zeroes(f, d, height(r) - 1)[i]
    {
        var p := natToBitList(|l| - 1, height(r));
        bitToNatToBitsIsIdentity(|l| - 1, height(r));
        assert(bitListToNat(p) == |l| - 1);
        rightSiblingsOfLastPathAreDefault(p, r, |l| - 1, f, 0, d);
    }
}
