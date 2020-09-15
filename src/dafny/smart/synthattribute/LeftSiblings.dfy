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
 
// include "../intdiffalgo/DiffTree.dfy"
include "../trees/CompleteTrees.dfy"
include "../helpers/Helpers.dfy"
include "../paths/PathInCompleteTrees.dfy"
include "../seqofbits/SeqOfBits.dfy"
include "../helpers/SeqHelpers.dfy"
include "../trees/Trees.dfy"
include "./LeftSiblingsPlus.dfy"

module LeftSiblings {
 
    // import opened DiffTree
    import opened CompleteTrees
    import opened Helpers
    import opened PathInCompleteTrees
    import opened SeqOfBits
    import opened SeqHelpers
    import opened Trees
    import opened LeftSiblingsPlus

    /**
     *  If b and b' agree on values at which p[i] == 1 and b has siblings at p[..], then 
     *  b' has siblings at same location.  
     */
    // lemma {:induction p, r} siblingsLeft(p : seq<bit>, r : Tree<int>, b : seq<int>, b': seq<int>, k : nat, i : nat) 

    //     requires isCompleteTree(r)
    //     /** `r` is decorated with attribute `f`. */
    //     requires isDecoratedWith(diff, r)
    //     requires height(r) >= 1

    //     /**  all leaves after the k leaf are zero. */
    //     requires k < |leavesIn(r)|
    //     requires forall i :: k < i < |leavesIn(r)| ==> leavesIn(r)[i].v == 0

    //     /** p is the path to k leaf in r. */
    //     requires hasLeavesIndexedFrom(r, i)
    //     requires |p| == height(r)
    //     requires nodeAt(p, r) == leavesIn(r)[k]

    //     requires |b| == |p|
    //     /** `b` contains values at left siblings on path `p`. */
    //     requires forall i :: 0 <= i < |b| ==> p[i] == 1 ==> b[i] == siblingAt(take(p, i + 1), r).v

    //     /** b and b' agree on values at indices where p[i] == 1, and otherwise b'[i] == 0 */
    //     requires |b'| == |b| && forall i :: 0 <= i < |b'| ==> if p[i] == 1 then b'[i] == b[i] else b'[i] == 0 

    //     ensures forall i :: 0 <= i < |b'| ==> b'[i] == siblingAt(take(p, i + 1), r).v
    // {
    //     leavesRightOfNodeAtPathZeroImpliesRightSiblingsOnPathZero(r, k, p, i);   
    // }

    /**
     *  Let two trees r and r' (same height) that agree on all values of their leaves except possibly at k.
     *  Let p be the path to the k-th leaf.
     *  Then the values on the i-th left siblings of p in r is equal to the values on the i-th left siblings of p in r'.
     *
     *  @param  p       A path to a leaf.
     *  @param  r       A tree.
     *  @param  r'      A tree.
     *  @param  k       The index of a leaf in r and r'.
     *  @param  f       The synthesised attribute to decorate the trees.
     *  @param  i       An index on the path p.
     *  @param  index   The initial value of the indexing of leaves in r and r'.
     */
    lemma {:induction p, r, r'} leftSiblingsInEquivTrees<T>(p : seq<bit>, r : Tree<T>, r' : Tree<T>, k: nat, f: (T, T) -> T, i: nat, index: nat)

        requires isCompleteTree(r)
        requires isCompleteTree(r')
        requires isDecoratedWith(f, r)
        requires isDecoratedWith(f, r')
        requires height(r) == height(r') >= 1
        requires hasLeavesIndexedFrom(r, index)
        requires hasLeavesIndexedFrom(r', index)

        requires 1 <= |p| == height(r)

        requires k < |leavesIn(r)| == |leavesIn(r')|
        requires take(leavesIn(r), k) == take(leavesIn(r'), k)
        requires drop(leavesIn(r), k + 1) == drop(leavesIn(r'), k + 1)

        requires bitListToNat(p) == k 
 
        requires 0 <= i < |p|
        ensures siblingAt(take(p, i + 1), r).v == siblingAt(take(p, i + 1), r').v

        decreases p, r, r' 
    {
            assert(isCompleteTree(r));
            assert(isCompleteTree(r'));
            childrenInCompTreesHaveSameNumberOfLeaves(r);
            childrenInCompTreesHaveSameNumberOfLeaves(r');

            match (r, r')
                case (Node(_, lc, rc), Node(_, lc', rc')) =>
                //  Prove some properties that guarantee pre-conditions of
                //  functions/lemmas called in the proof.
                completeTreeNumberLemmas(r);
                assert(power2(height(r)) == |leavesIn(r)|);

            if |p| == 1 {
                //  Thanks Dafny
            } else {
                childrenCompTreeValidIndex(r, height(r), index);
                childrenCompTreeValidIndex(r', height(r'), index);

                childrenInCompTreesHaveHalfNumberOfLeaves(r, height(r));
                childrenInCompTreesHaveHalfNumberOfLeaves(r', height(r'));

                completeTreeNumberLemmas(r);
                completeTreeNumberLemmas(r');
                
                leafAtPathIsIntValueOfPath(p, r, k, index);
                leafAtPathIsIntValueOfPath(p, r', k, index);
                assert(nodeAt(p, r) == leavesIn(r)[k]);
                assert(nodeAt(p, r') == leavesIn(r')[k]);

                if first(p) == 0 {
                    //  sibling is the right node (rc, rc'), but path leads to left nodes.
                    //  So all leaves in right trees are equal.
                    //  Prove that k < power2(height(r) - 1)
                    initPathDeterminesIndex(r, p, k, index);
                    
                    assert(k < power2(height(r)) / 2);
                    assert(k < |leavesIn(lc)| == |leavesIn(lc')|);
                    //  Prove property for siblingAt(take(p, i + 1)).v in left trees by induction
                    //  and first sibling is rc (rc') using sameLeavesSameRoot
                    if (i >= 1) {
                         leftSiblingsInEquivTreesNonBaseCaseFirstLeft(p, r, r', k, f, i, index);
                        calc == {
                            siblingAt(take(p,i + 1), r).v;
                            siblingAt(take(tail(p), i), lc).v;
                            { 
                                leftSiblingsInEquivTrees(tail(p), lc, lc', k, f, i - 1, index); 
                            }
                            siblingAt(take(tail(p), i), lc').v;
                            siblingAt(take(p,i + 1), r').v;
                        }
                        assert(siblingAt(take(p,i + 1), r).v == siblingAt(take(p,i + 1), r').v);
                    } else {
                        assert(i == 0);
                        leftSiblingsInEquivTreesBaseCase(p, r, r', k, f, index);
                    }
                } else {
                    //  Prove property for siblingAt(take(p, i + 1)).v in right trees by induction
                    //  and first sibling is lc (lc') using sameLeavesSameRoot
                    //  Prove that k >= power2(height(r) - 1)
                    initPathDeterminesIndex(r, p, k, index);
                    assert(k >= power2(height(r)) / 2);

                    if (i >= 1) {
                        var k' := k  - power2(height(r)) / 2;
                        assert(k + 1 >  power2(height(r)) / 2);
 
                        leftSiblingsInEquivTreesNonBaseCaseFirstRight(p, r, r', k, f, i, index);
                        calc == {
                            siblingAt(take(p,i + 1), r).v;
                            siblingAt(take(tail(p), i), rc).v;
                            { 
                                leftSiblingsInEquivTrees(tail(p), rc, rc', k - power2(height(r)) / 2, f, i - 1, index + power2(height(r)) / 2); 
                            }
                            siblingAt(take(tail(p), i), rc').v;
                            siblingAt(take(p,i + 1), r').v;
                        }
                        assert(siblingAt(take(p,i + 1), r).v == siblingAt(take(p,i + 1), r').v);
                    } else {
                        assert(i == 0);
                        leftSiblingsInEquivTreesBaseCase(p, r, r', k, f, index);
                    }
                }
        }
    }

     lemma {:induction p, r, r'} leftSiblingsInEquivTrees2<T>(p : seq<bit>, r : Tree<T>, r' : Tree<T>, k: nat, f: (T, T) -> T, index: nat)

        requires isCompleteTree(r)
        requires isCompleteTree(r')
        requires isDecoratedWith(f, r)
        requires isDecoratedWith(f, r')
        requires height(r) == height(r') >= 1
        requires hasLeavesIndexedFrom(r, index)
        requires hasLeavesIndexedFrom(r', index)

        requires 1 <= |p| == height(r)

        requires k < |leavesIn(r)| == |leavesIn(r')|
        requires take(leavesIn(r), k) == take(leavesIn(r'), k)
        requires drop(leavesIn(r), k + 1) == drop(leavesIn(r'), k + 1)

        requires bitListToNat(p) == k 

        ensures forall i :: 0 <= i < |p| ==> 
            siblingAt(take(p, i + 1), r).v == siblingAt(take(p, i + 1), r').v
    {
        forall ( i : nat | 0 <= i < |p|) 
            ensures siblingAt(take(p, i + 1), r).v == siblingAt(take(p, i + 1), r').v
        {
            leftSiblingsInEquivTrees(p, r, r', k, f, i, index);
        }
    }
 }