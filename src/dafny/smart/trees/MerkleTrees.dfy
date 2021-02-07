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
include "../trees/Trees.dfy"
include "../trees/CompleteTrees.dfy"
include "../synthattribute/ComputeRootPath.dfy"
include "../paths/PathInCompleteTrees.dfy"
include "../paths/NextPathInCompleteTreesLemmas.dfy"
include "../synthattribute/Siblings.dfy"
include "../synthattribute/RightSiblings.dfy"
include "../seqofbits/SeqOfBits.dfy"
include "../helpers/SeqHelpers.dfy"
include "../algorithms/IndexBasedAlgorithm.dfy"

/**
 *  Provide Merkle trees which are trees decorated with a synthesised attribute.
 */
module MerkleTrees {

    import opened Helpers
    import opened Trees
    import opened CompleteTrees
    import opened ComputeRootPath
    import opened PathInCompleteTrees
    import opened Siblings
    import opened RSiblings
    import opened SeqOfBits
    import opened SeqHelpers
    import opened NextPathInCompleteTreesLemmas
    import opened IndexBasedAlgorithm

    ///////////////////////////////////////////////////////////////////////////
    //  Main predicates and functiona.
    ///////////////////////////////////////////////////////////////////////////
   /** 
    *   Defines the Merkle Tree associated with a given sequence.
    *  
    *   @note       This function does not algorithmically compute the tree but rather
    *               defines the properties of the result.
    *
    *   @param  l   A list of values.
    *   @param  h   A height.
    *   @param  f   A function to combine two values.
    *   @param  d   A default value for the leaves not in `l`.
    *   @returns    The Merkle tree of height `h` that corresponds to `l`.
    */
    function {:axiom} buildMerkle<T>(l: seq<T>, h : nat, f : (T, T) -> T, d : T) : Tree<T> 
        /** Tree has enough leaves to store `l`. */
        requires |l| <= power2(h)      

        ensures height(buildMerkle(l, h, f, d)) == h
        ensures |leavesIn(buildMerkle(l, h, f, d))| == power2(h)  
        ensures isMerkle(buildMerkle(l, h, f, d), l, f, d)
        ensures hasLeavesIndexedFrom(buildMerkle(l, h, f, d), 0)

    /**
     *  Whether the tree is a Merkle Tree.
     *
     *  The tree must be:
     *      1.  complete
     *      2.  the first |l| leftmost leaves hold the values of `l`,
     *      3.  the leaves after |l| hold a default value `default`, 
     *      4.  the values on the internal nodes correspond to the value of
     *          synthesised attribute `f`.
     *
     *  @param  root    A tree.
     *  @param  l       A list, with the value sof the leftmost leaves.
     *  @param  f       A binary function.
     *  @param  default A default value for the rightmost leaves. 
     */
    predicate isMerkle<T>(root: Tree<T>, l: seq<T>, f : (T, T) -> T, default: T) 
        requires |l|  <= power2(height(root))
    {
        isCompleteTree(root)
        && isDecoratedWith(f, root)
        && leftLeavesMatch(l, root, default)
    }

    /**
     *  The |l| leftmost leaves of root are equal to l.
     *  
     *  @param  l           A list of elements.
     *  @param  root        A tree.
     *  @param  default     The default value for right-padding the tree leaves.
     *
     *  We assume leavesIn return an indexed (from left to right) list of leaves.
     */
    predicate leftLeavesMatch<T>(l: seq<T>, root: Tree<T>, default: T)
        requires isCompleteTree(root)
        requires |l| <= power2(height(root))
    {
        completeTreeNumberLemmas(root);
        assert(|l| <= |leavesIn(root)|);
        forall i:: 
            (0 <= i < |l| ==> l[i] == leavesIn(root)[i].v)
            && 
            (|l| <= i < |leavesIn(root)|  ==> leavesIn(root)[i].v == default)
    }

    ///////////////////////////////////////////////////////////////////////////
    //  Main properties.
    ///////////////////////////////////////////////////////////////////////////

    /**
     *  Left and right contains siblings of path to k-th leaf in r.
     *
     *  @param  k       The index of a leaf in the tree `r`.
     *  @param  r       A tree.
     *  @param  left    A vector of values.
     *  @param  right   A vector of values.
     *  @returns        True if and only if the left (resp. right) siblings on the path 
     *                  to k-th lefa in `r` have values in `left` (resp. `right`). 
     */
    predicate areSiblingsAtIndex<T>(k : nat, r : Tree<T>, left : seq<T>, right : seq<T>)
        requires hasLeavesIndexedFrom(r, 0) 
        requires isCompleteTree(r)
        requires height(r) >= 1
        requires k < power2(height(r)) 
        requires |left| == |right| == height(r)
    {
        //  Defien the path to k-th leaf.
        var p := natToBitList(k, height(r));
        //  Property of siblings.
        forall i :: 0 <= i < |p| ==>
            siblingValueAt(p, r, i + 1) == 
                if p[i] == 0 then 
                    right[i]
                else 
                    left[i]
    }

    /**
     *  computeLeftSiblingsOnNextpathWithIndex returns the siblings on the next tree.
     *
     *  @param  h       The height of the trees.
     *  @param  a       The element inserted in the tree.
     *  @param  l       The list of values.
     *  @param  left    The values left of path to |l|.
     *  @param  right   The values right of path to |l|.
     *  @param  f       The synthesised attribute to compute.
     *  @param  d       The default value for type T.
     *
     */
    lemma {:induction false} computeNewLeftIsCorrect<T>(
            l: seq<T>, a : T, h : nat, left : seq<T>, right : seq<T>, f : (T, T) -> T, d : T) 
        requires 1 <= h 
        requires |l| < power2(h) - 1
        requires |left| == |right| == h 
        requires right == zeroes(f, d, h - 1)
        requires areSiblingsAtIndex(|l|, buildMerkle(l, h, f, d), left, right)

        ensures areSiblingsAtIndex(
            |l| + 1, buildMerkle(l + [a], h, f, d), 
            computeLeftSiblingsOnNextpathWithIndex(h, |l|, left, right, f, a),
            right
        )
    {
        //  Get path to |l|-th element as seq<bit> and prove it has zero.
        var p := natToBitList(|l|, h);
        bitToNatToBitsIsIdentity(|l|, h);
        pathToNoLasthasZero(p);

        //  The trees for `l` and `l` + [a].
        var prevTree := buildMerkle(l, h, f, d);
        var nextTree := buildMerkle(l + [a], h, f, d);

        //  The siblings of p in buildMerkle(l + [a], h, f, d) are 
        //  the same as siblings on p in buildMerkle(l, h, f, d)
        reveal_siblingValueAt();
        siblingsForNextList(h, l, a, prevTree, nextTree, f, d, p);

        //  compute next left siblings in nextTree
        completeTreeNumberLemmas(nextTree);
        indexOfLeafisIntValueOfPath(p, nextTree, |l|);
        assert(nodeAt(p,nextTree).v == leavesIn(buildMerkle(l + [a], h, f, d))[|l|].v == a);
        computeLeftSiblingOnNextPathFromLeftRightIsCorrectInATree(p, nextTree, left, right, f, a, |l|);

        //  NextPath(p) is the binary representation of |l| + 1.
        pathToSucc(p, |l|, h);
        assert(nextPath(p) == natToBitList(|l| + 1, h));

        //  Right siblings are still zeroes
        rightOfPathToLastIsZero(nextPath(p), l + [a],nextTree, f, d);
    }

    /** 
     *  Compute root value for path to |l|-th leaf is correct.
     *
     *  @param  h       The height of the trees.
     *  @param  a       The element inserted in the tree.
     *  @param  l       The list of values.
     *  @param  left    The values left of path to |l|.
     *  @param  right   The values right of path to |l|.
     *  @param  f       The synthesised attribute to compute.
     *  @param  d       The default value for type T.
     */
    lemma {:induction false} computeRootIsCorrect<T>(
            l: seq<T>, h : nat, left : seq<T>, right : seq<T>, f : (T, T) -> T, d : T) 
        requires 1 <= h 
        requires |l| < power2(h) 
        requires |left| == |right| == h 
        requires right == zeroes(f, d, h - 1)
        requires areSiblingsAtIndex(|l|, buildMerkle(l, h, f, d), left, right)

        ensures computeRootLeftRightUpWithIndex(h, |l|, left, right, f, d) == buildMerkle(l, h, f, d).v 
    {    
        var p := natToBitList(|l|, h);
        bitToNatToBitsIsIdentity(|l|, h);
        assert(bitListToNat(p) == |l|);
        
        var r := buildMerkle(l, h, f, d);
        completeTreeNumberLemmas(r);
        leafAtPathIsIntValueOfPath(p, r, |l|, 0);
        assert(nodeAt(p, r).v == leavesIn(r)[|l|].v);
        assert(leavesIn(r)[|l|].v == d);
        reveal_siblingValueAt();
        computeRootLeftRightUpIsCorrectForTree(p, r, left, right, f, d);
    }

    /**
     *  The right siblings of the path to the last element of the list are
     *  zeroes.  
     *
     *  @param  l   A list of values.
     *  @param  r   A merkle tree for l.
     *  @param  f   A function to combine values.
     *  @param  d   A default value for the leaves not in `l`.
     */
    lemma {:induction false} rightOfPathToLastIsZero<T>(p : seq<bit>, l: seq<T>, r: Tree<T>, f : (T, T) -> T, d : T) 
        requires hasLeavesIndexedFrom(r, 0) 
        requires height(r) >= 1
        requires |l| < power2(height(r))
        requires isMerkle(r, l, f, d)

        requires p == natToBitList(|l|, height(r))
        ensures forall i :: 0 <= i < |p| && p[i] == 0 ==> 
                siblingValueAt(p, r, i + 1) == zeroes(f, d, height(r) - 1)[i]
    {
        bitToNatToBitsIsIdentity(|l|, height(r));
        assert(bitListToNat(p) == |l|);
        completeTreeNumberLemmas(r);
        assert(|l| <= |leavesIn(r)|);        
        rightSiblingsOfLastPathAreDefault(p, r, |l|, f, 0, d);
    }

    /**
     *  Siblings relation in two adjacent trees.
     *  The values of the siblings in MKL(l) for the path to leaf right after last(l), are equal
     *  to the values of the siblings of the path to [a] in MKL(l + [a]).
     *
     *  @param  h   The height of the trees.
     *  @param  l   The list of values.
     *  @param  a   The element inserted in the tree.
     *  @param  r   A merkle tree for l.
     *  @param  r'  A merkle tree for l + [a].
     *  @param  f   The synthesised attribute to compute.
     *  @param  d   The default value for type T.
     *  @param  p   The path to the the (|l| + 1)-th leaf (at index |l|).
     */
    lemma {:induction false} siblingsForNextList<T>(
        h : nat, l: seq<T>, a : T, r : Tree<T>, r' : Tree<T>, f : (T, T) -> T, d : T, p : seq<bit>) 

        /** The list does not fill up the leaves of the tree.  */
        requires 0 <= |l| < power2(h) - 1
        /** Trees requirements. */ 
        requires 1 <= h == height(r) == height(r') == h 
        requires isCompleteTree(r) && isCompleteTree(r')
        requires hasLeavesIndexedFrom(r, 0) && hasLeavesIndexedFrom(r', 0)
        requires isMerkle(r, l, f, d) && isMerkle(r', l + [a], f, d);

        /** p is the path to the (|l| = 1)-th leaf with value 0 in r and a in r'. */
        requires p == natToBitList(|l|, h);
        
        ensures forall i :: 0 <= i < |p|  ==>
                siblingValueAt(p, r', i + 1) == siblingValueAt(p, r, i + 1)

    {
        var k := |l|;
        completeTreeNumberLemmas(r);
        completeTreeNumberLemmas(r');
        assert(k == |l| < |leavesIn(r)| == |leavesIn(r')| );

        equivTreesSameLeaves(h, l, a, r, r', f, d);
        assert(takeLeavesIn(r, k) == takeLeavesIn(r', k));
        assert(dropLeavesIn(r, k + 1) == dropLeavesIn(r', k + 1));

        calc == {
            bitListToNat(p);
            bitListToNat(natToBitList(|l|, h));
            { bitToNatToBitsIsIdentity(|l|, h); }
            |l|;
        }

        //  Apply lemma siblingsInEquivTrees
        assert(bitListToNat(p) == k);
        assert(isDecoratedWith(f, r) && isDecoratedWith(f, r'));
        assert (|p| == height(r));

        siblingsInEquivTrees(p, r, r', k, f, 0);
        reveal_siblingValueAt();
        assert(forall i :: 0 <= i < |p| ==> siblingValueAt(p, r, i + 1) == siblingValueAt(p, r', i + 1));
    }

    ///////////////////////////////////////////////////////////////////////////
    //  Helper lemmas and functions.
    ///////////////////////////////////////////////////////////////////////////

    /**
     *  MKL(l) and MKL(l + [a]) have same leaves upto from 0 to |l| - 1 and
     *  from |l| + 1 to 2^{height(tree)}.
     *
     *  @param  h   The height of the trees.
     *  @param  l   The list of values.
     *  @param  a   The element inserted in the tree.
     *  @param  r   A merkle tree for l.
     *  @param  r'  A merkle tree for l + [a].
     *  @param  f   The synthesised attribute to compute.
     *  @param  d   The default value for type T.
     */
    lemma {:induction false} equivTreesSameLeaves<T>(h : nat, l: seq<T>, a : T, r : Tree<T>, r' : Tree<T>, f : (T, T) -> T, d : T) 
        /** The list does not fill up the leaves of the tree.  */
        requires 0 <= |l| < power2(h) - 1

        /** Trees requirements. */ 
        requires 1 <= h == height(r) == height(r') == h 
        requires isCompleteTree(r) && isCompleteTree(r')
        requires hasLeavesIndexedFrom(r, 0) && hasLeavesIndexedFrom(r', 0)
        requires isMerkle(r, l, f, d) && isMerkle(r', l + [a], f, d);
    
        ensures |l| + 1 < |leavesIn(r)| == |leavesIn(r')|
        ensures takeLeavesIn(r, |l|) == takeLeavesIn(r', |l|)
        ensures dropLeavesIn(r, |l| + 1) == dropLeavesIn(r', |l| + 1)

    {
        completeTreeNumberLemmas(r);
        completeTreeNumberLemmas(r');
        
        //  All leaves have same index
        forall (i : nat | 0 <= i < power2(h) - 1) 
            ensures leavesIn(r)[i].index == leavesIn(r')[i].index
        {
            calc == {
                leavesIn(r)[i].index ;
                i;
                leavesIn(r)[i].index ;
            }
        }

        //  All leaves except at |l|  have the same value.
        forall (i : nat | 0 <= i <  power2(h) - 1) 
            ensures i != |l| ==> leavesIn(r)[i].v == leavesIn(r')[i].v
        {
            if i < |l| {
                calc == {
                    leavesIn(r)[i].v;
                    l[i];
                    leavesIn(r')[i].v;
                }
            } 
            if i > |l| {
                 calc == {
                    leavesIn(r)[i].v;
                    d;
                    leavesIn(r')[i].v;
                }
            }
            calc == {
                leavesIn(r)[i].index ;
                i;
                leavesIn(r)[i].index ;
            }
        }
        reveal_takeLeavesIn();
        reveal_dropLeavesIn();
        assert  takeLeavesIn(r, |l|) == takeLeavesIn(r', |l|);
        assert  dropLeavesIn(r, |l| + 1) == dropLeavesIn(r', |l| + 1);
    }

}
