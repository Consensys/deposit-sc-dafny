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
include "synthattribute/Siblings.dfy"
include "synthattribute/RightSiblings.dfy"
include "seqofbits/SeqOfBits.dfy"
include "helpers/SeqHelpers.dfy"

module MerkleTrees {

    import opened Helpers
    import opened Trees
    import opened CompleteTrees
    import opened PathInCompleteTrees
    import opened Siblings
    import opened RSiblings
    import opened SeqOfBits
    import opened SeqHelpers

    ///////////////////////////////////////////////////////////////////////////
    //  Main predicates and functiona.
    ///////////////////////////////////////////////////////////////////////////

    /**
     *  Whether the tree is a Merkle Tree.
     *
     *  The tree must be:
     *      1.  complete
     *      2.  the first |l| leftmost leaves hold the values of `l`
     *      3.  the leaves after |l| hold a default value `default`, 
     *      4.  the values on the internal nodes correspond to the value of
     *          synthesied attribute `f`.
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
        && treeLeftmostLeavesMatchList(l, root, default)
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
        /** Tree has enough leaves to store `l`. */
        requires |l| <= power2(h)      

        ensures height(buildMerkle(l, h, f, d)) == h
        ensures |leavesIn(buildMerkle(l, h, f, d))| == power2(h)  
        ensures isMerkle(buildMerkle(l, h, f, d), l, f, d)

    /**
     *  The |l| leftmost leaves of root are equal to l.
     *  
     *  @param  l           A list of elements.
     *  @param  root        A tree.
     *  @param  default     The default value for right-padding the tree leaves.
     *
     *  We assume leavesIn return an indexed (from left to right) list of leaves.
     */
    predicate treeLeftmostLeavesMatchList<T>(l: seq<T>, root: Tree<T>, default: T)
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
        completeTreeNumberLemmas(r);
        assert(|l| <= |leavesIn(r)|);        
        rightSiblingsOfLastPathAreDefault(p, r, |l| - 1, f, 0, d);
    }

    /**
     *  Left siblings relation in two adjacent trees.
     *  The values of left siblings in MKL(l) for the path to leaf right after last(l), are equal
     *  to the values of the left siblings of the path to [a] in MKL(l + [a]).
     *
     *  @param  h   The height of the trees.
     *  @param  l   The list of values.
     *  @param  a   The element inserted in the tree.
     *  @param  r   A merkle tree for l.
     *  @param  r'  A merkle tree for l + [a].
     *  @param  f   The synthesised attribute to compute.
     *  @param  d   The default value for type T.
     *  @param  p   The path to the the |l|-th leaf.
     *  @param  p'  The path to the the (|l| + 1)-th leaf.
     */

    lemma {:induction l} nextPathSameSiblingsInNextList<T>(h : nat, l: seq<T>, a : T, r : Tree<T>, r' : Tree<T>, f : (T, T) -> T, d : T, p : seq<bit>, p' : seq<bit>) 
        /** The list does not fill up the leaves of the tree.  */
        requires 0 <= |l| < power2(h) - 1

        /** Trees requirements. */ 
        requires 1 <= h == height(r) == height(r') == h 
        requires isCompleteTree(r) && isCompleteTree(r')
        requires hasLeavesIndexedFrom(r, 0) && hasLeavesIndexedFrom(r', 0)
        requires isMerkle(r, l, f, d) && isMerkle(r', l + [a], f, d);

        /** Path `p` is to the (|l| -1)-th leaf indexed |l| - 1, p` to the |l|-th leaf i.e indexed |l|. */
        requires |l| >= 1 ==> p  == natToBitList(|l| - 1, h);
        requires p' == natToBitList(|l|, h);
        
        /** if |l| >= 1 then `p` has a zero. */
        /** And hence we can compute nextpath(p), which is p'. */
        ensures |l| >= 1 ==> exists i :: 0 <= i < |p| && p[i] == 0
        ensures |l| >= 1 ==> p' == nextPath(p)

        /**  */
        ensures 
            (|l| >= 1 && forall i :: 0 <= i < |p'|  ==>
                siblingValueAt(p', r', i + 1) == siblingValueAt(nextPath(p), r, i + 1)
            )
            ||
            (|l| == 0 ==>  forall i :: 0 <= i < |p'| ==> p'[i] == 0)

    {
        if |l| == 0 {
            //  In this case, p' is a path to first leaf indexed 0 and  p' = [0,0,0 ...0]
            //  So the premise  p'[i] == 1 is always false
            calc == {
                bitListToNat(p');
                bitListToNat(natToBitList(|l|, h));
                { bitToNatToBitsIsIdentity(|l|, h); }
                |l|;
                0;
            }
            valueIsZeroImpliesAllZeroes(p');
            assert(forall i :: 0 <= i < |p'| ==> 
                p'[i] == 0
            );
        } else {
            bitToNatToBitsIsIdentity(|l| - 1, h);
            assert(bitListToNat(p) == |l| - 1);
            bitToNatToBitsIsIdentity(|l|, h);
            assert(bitListToNat(p') == |l|);

            //  Show that p has a zero.
            pathToNoLasthasZero(p);
        
            //  Show that p' is actually nextPath(p)
            succIsNextPath(p, p');

            //  Siblings values in nextPath(p) in r and p' in r' are related.
            //  Prove pre-conditions for applying lemma siblingsInEquivTrees
            var k := |l|;
            //  k < |leavesIn(r)| == |leavesIn(r')| 
            completeTreeNumberLemmas(r);
            completeTreeNumberLemmas(r');
            assert(k < |leavesIn(r)| == |leavesIn(r')| );

            //  takeLeavesIn(r, k) == takeLeavesIn(r', k)
            //  dropLeavesIn(r, k + 1) == dropLeavesIn(r', k + 1)
            equivTreesSameLeaves(h, l, a, r, r', f, d);
            assert(takeLeavesIn(r, k) == takeLeavesIn(r', k));
            assert(dropLeavesIn(r, k + 1) == dropLeavesIn(r', k + 1));

            //  bitListToNat(p') == k 
            calc == {
                bitListToNat(p');
                bitListToNat(natToBitList(|l|, h));
                { bitToNatToBitsIsIdentity(|l|, h); }
                |l|;
            }

            //  Apply lemma siblingsInEquivTrees
            assert(bitListToNat(p') == k);

            reveal_siblingValueAt();
            siblingsInEquivTrees(p', r, r', k, f, 0);
            assert(forall i :: 0 <= i < |p'| ==> siblingValueAt(p', r, i + 1) == siblingValueAt(p', r', i + 1));
        }
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

    lemma equivTreesSameLeaves<T>(h : nat, l: seq<T>, a : T, r : Tree<T>, r' : Tree<T>, f : (T, T) -> T, d : T) 
        /** The list does not fill up the leaves of the tree.  */
        requires 0 <= |l| < power2(h) - 1

        /** Trees requirements. */ 
        requires 1 <= h == height(r) == height(r') == h 
        requires isCompleteTree(r) && isCompleteTree(r')
        requires hasLeavesIndexedFrom(r, 0) && hasLeavesIndexedFrom(r', 0)
        requires isMerkle(r, l, f, d) && isMerkle(r', l + [a], f, d);
    
        ensures |l| + 1 < |leavesIn(r)| == |leavesIn(r')|
        ensures  takeLeavesIn(r, |l|) == takeLeavesIn(r', |l|)
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
            } else if i > |l| {
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
    // predicate isMerkle2<T>(root: Tree<T>, l: seq<T>, f : (T, T) -> T) 
    //     requires |l| == |leavesIn(root)|
    // {
    //     isCompleteTree(root)
    //     && isDecoratedWith(f, root)                                     
    //     && forall i :: 0 <= i < |l| ==> l[i] == leavesIn(root)[i].v                
    // }

    /**
     *  For tree of height >= 1, Merkle projects onto lc and rc for 
     *  split list. 
     *
     *  @param  root    A complete tree.
     *  @param  l       A list of values.
     *  @param  f       A binary operation.
     *  @param  h       The height of the tree.
     *  @returns        True if and only if the tree is decorated with f
     *                  and the leaves's values agree with `l`.
     */
    // lemma {:induction h} treeIsMerkleImpliesChildrenAreMerkle<T>(r: Tree<T>, l: seq<T>, f : (T, T) -> T, h : nat, d : T)
    //     requires |l| == |leavesIn(r)|
    //     requires isMerkle(r, l, f, d : T)
    //     requires h == height(r) >= 1
    //     ensures |l| == power2(height(r) )
    //     ensures match r 
    //         case Node(_, lc, rc) =>
    //             |leavesIn(lc)| == power2(height(r))/2
    //             && |l[.. power2(height(r))/2]| <=  |leavesIn(lc)|
    //             && isMerkle(lc, l[..  power2(height(r))/2], f)
    //             && |leavesIn(rc)| == power2(height(r))/2
    //             && |l[power2(height(r))/2..]| <=  |leavesIn(rc)|
    //             && isMerkle(rc, l[power2(height(r))/2..], f)
    // {
    //     reveal_power2();
    //     childrenInCompTreesHaveHalfNumberOfLeaves(r, h);
    // }
    
}
