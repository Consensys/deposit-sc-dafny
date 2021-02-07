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
 
include "../trees/CompleteTrees.dfy"
include "../helpers/Helpers.dfy"
include "../paths/PathInCompleteTrees.dfy"
include "../seqofbits/SeqOfBits.dfy"
include "../helpers/SeqHelpers.dfy"
include "../trees/Trees.dfy"
include "./SiblingsPlus.dfy"

module Siblings {
 
    // import opened DiffTree
    import opened CompleteTrees
    import opened Helpers
    import opened PathInCompleteTrees
    import opened SeqOfBits
    import opened SeqHelpers
    import opened Trees
    import opened SiblingsPlus 

    /**
     *  Let two trees r and r' (same height) that agree on all values of their leaves except possibly at k.
     *  Let p be the path to the k-th leaf.
     *  Then the value on every i-th sibling of p in r is equal to the value on the i-th sibling of p in r'.
     *
     *  @param  p       A path to the k-th leaf..
     *  @param  r       A tree.
     *  @param  r'      A tree.
     *  @param  k       The index of a leaf in r and r'.
     *  @param  f       The synthesised attribute to decorate the trees.
     *  @param  index   The initial value of the indexing of leaves in r and r'.
     */
    lemma {:induction p, r, r'} siblingsInEquivTrees<T>(p : seq<bit>, r : Tree<T>, r' : Tree<T>, k: nat, f: (T, T) -> T, index: nat)

        requires isCompleteTree(r) && isCompleteTree(r')
        requires isDecoratedWith(f, r) && isDecoratedWith(f, r')
        requires height(r) == height(r') >= 1
        requires hasLeavesIndexedFrom(r, index) && hasLeavesIndexedFrom(r', index)

        requires 1 <= |p| == height(r)

        requires k < |leavesIn(r)| == |leavesIn(r')|
        requires takeLeavesIn(r, k) == takeLeavesIn(r', k)
        requires dropLeavesIn(r, k + 1) == dropLeavesIn(r', k + 1)

        requires bitListToNat(p) == k 

        ensures forall i :: 0 <= i < |p| ==> siblingValueAt(p, r, i + 1) == siblingValueAt(p, r', i + 1)
    {
        forall ( i : nat | 0 <= i < |p|) 
            ensures siblingValueAt(p, r, i + 1) == siblingValueAt(p, r', i + 1)
        {
            //  Apply lemma for each index
            siblingsInEquivTreesAreEqual(p, r, r', k, f, i, index);
        }
        reveal_siblingValueAt();
    }    

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
    lemma {:induction p, r, r'} siblingsInEquivTreesAreEqual<T>(p : seq<bit>, r : Tree<T>, r' : Tree<T>, k: nat, f: (T, T) -> T, i: nat, index: nat)

        requires isCompleteTree(r) && isCompleteTree(r')
        requires isDecoratedWith(f, r) && isDecoratedWith(f, r')
        requires height(r) == height(r') >= 1
        requires hasLeavesIndexedFrom(r, index) && hasLeavesIndexedFrom(r', index)

        requires k < |leavesIn(r)| == |leavesIn(r')|
        requires takeLeavesIn(r, k) == takeLeavesIn(r', k)
        requires dropLeavesIn(r, k + 1) == dropLeavesIn(r', k + 1)

        requires 1 <= |p| == height(r)
        requires bitListToNat(p) == k 
 
        requires 0 <= i < |p|
        ensures siblingValueAt(p, r, i + 1) == siblingValueAt(p, r', i + 1)

        decreases p, r, r' 
    {
        reveal_takeLeavesIn();
        reveal_siblingValueAt();
        reveal_dropLeavesIn();

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
                assert(i == 0);
                siblingsInEquivTreesBaseCase(p, r, r', k, f, index);
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
                    //  Prove that k < power2(height(r))
                    initPathDeterminesIndex(r, p, k, index);
                    assert(k < power2(height(r)) / 2);
                    assert(k < |leavesIn(lc)| == |leavesIn(lc')|);
                    //  Prove property for siblingAt(take(p, i + 1)).v in left trees by induction
                    //  and first sibling is rc (rc') using sameLeavesSameRoot
                    if (i >= 1) {
                        siblingsInEquivTreesNonBaseCaseFirstLeft(p, r, r', k, f, i, index);
                        calc == {
                            siblingAt(take(p,i + 1), r).v;
                            siblingAt(take(tail(p), i), lc).v;
                            { 
                                siblingsInEquivTreesAreEqual(tail(p), lc, lc', k, f, i - 1, index); 
                            }
                            siblingAt(take(tail(p), i), lc').v;
                            siblingAt(take(p,i + 1), r').v;
                        }
                        assert(siblingAt(take(p,i + 1), r).v == siblingAt(take(p,i + 1), r').v);
                    } else {
                        assert(i == 0);
                        siblingsInEquivTreesBaseCase(p, r, r', k, f, index);
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
 
                        siblingsInEquivTreesNonBaseCaseFirstRight(p, r, r', k, f, i, index);
                        calc == {
                            siblingValueAt(p, r, i + 1);
                            { reveal_siblingValueAt() ; }
                            siblingAt(take(p,i + 1), r).v;
                            { simplifySiblingAtIndexFirstBit(p, r, i + 1); }
                            siblingAt(take(tail(p), i), rc).v;
                            { 
                                siblingsInEquivTreesAreEqual(tail(p), rc, rc', k - power2(height(r)) / 2, f, i - 1, index + power2(height(r)) / 2); 
                            }
                            siblingAt(take(tail(p), i), rc').v;
                            { simplifySiblingAtIndexFirstBit(p, r', i + 1); }
                            siblingAt(take(p, i + 1), r').v;
                            { reveal_siblingValueAt() ; }
                            siblingValueAt(p, r', i + 1);
                        }
                    } else {
                        assert(i == 0);
                        siblingsInEquivTreesBaseCase(p, r, r', k, f, index);
                    }
                }
        }
    }


 }