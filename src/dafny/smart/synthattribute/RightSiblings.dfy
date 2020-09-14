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
 
include "../intdiffalgo/DiffTree.dfy"
include "../trees/CompleteTrees.dfy"
include "../helpers/Helpers.dfy"
include "../paths/PathInCompleteTrees.dfy"
include "../seqofbits/SeqOfBits.dfy"
include "../helpers/SeqHelpers.dfy"
include "../trees/Trees.dfy"
include "./LeftSiblingsPlus.dfy"

/**
 *  Provide proofs that right siblinbgs are constant in
 *  Merkle like trees.
 */
module RightSiblings {
 
    import opened DiffTree
    import opened CompleteTrees
    import opened Helpers
    import opened PathInCompleteTrees
    import opened SeqOfBits
    import opened SeqHelpers
    import opened Trees
    import opened LeftSiblingsPlus

    /**
     *  Default values on each evel of a tree.
     *
     *  Values are obtained by conbining the default values at level h - 1.
     *  @param  f   The synthesied attribute to compute.
     *  @param  d   The default value attached to the leaves.
     *  @param  h   The height of the tree.
     *
     */
    function defaultValue<T>(f: (T, T) -> T, d: T, h : nat) : T
        // ensures |defaultValues(f, d, h)| == h + 1
        decreases h
    {
        if h == 0 then 
            d
        else 
            var x := defaultValue(f, d, h - 1);
            f(x, x)
    }

    /**
     *  If all leaves are zero and tree is decorated with f, then
     *  root node is decorated with default value at height(r).
     */
    lemma {:induction r} allLeavesDefaultImplyRootNodeDefault<T>(r: Tree<T>, f: (T, T) -> T, d: T)
        requires isCompleteTree(r)
        requires isDecoratedWith(f, r)
        requires forall l :: l in leavesIn(r) ==> l.v == d
        ensures r.v == defaultValue(f, d, height(r))
    {   //  Thanks Dafny
        if height(r) == 0 {
            //  r is a leaf 
            assert(r.Leaf?);
            calc == {
                defaultValue(f, d, 0);
                d;
                r.v;
            }
        } else {
            match r
                case Node(_, lc, rc) => 
                //  Induction on left and richj children
                //  Leaves of left and right children are equal to d.
                childrenInCompTreesHaveHalfNumberOfLeaves(r, height(r));
                assert(leavesIn(lc) == leavesIn(r)[.. power2(height(r)) / 2]);
                assert(leavesIn(rc) == leavesIn(r)[power2(height(r)) / 2 ..]);
                //  Induction on lc and rc
                allLeavesDefaultImplyRootNodeDefault(lc, f, d);
                allLeavesDefaultImplyRootNodeDefault(rc, f, d);
                assert(lc.v == defaultValue(f, d, height(r) - 1));
                assert(rc.v == defaultValue(f, d, height(r) - 1));
                calc == {
                    r.v;
                    f(lc.v, rc.v);
                    f(defaultValue(f, d, height(r) - 1), defaultValue(f, d, height(r) - 1));
                    defaultValue(f, d, height(r));
                }
        }
    }

    /**
     *  Give a tree that corrrsponds to a list l, the path p to the leaf that corresponds
     *  to last(l), the roght siblings are constant (by leve in the tree).
     *    
     */
    lemma {:induction p, r} siblingsRightOfPathAreConstant<T>(p : seq<bit>, r : Tree<T>, k : nat, zeroes: seq<T>, f: (T, T) -> T, index : nat, d : T, i : nat) 

        requires isCompleteTree(r)
        requires isDecoratedWith(f, r)
        requires height(r) >= 0

        /**  all leaves after the k leaf are zero. */
        requires k < |leavesIn(r)|
        requires forall i :: k < i < |leavesIn(r)| ==> leavesIn(r)[i].v == d

        requires |zeroes| == |p| + 1
        // requires zeroes == defaultValues(f, d, height(r))

        /** p is the path to k leaf in r. */
        requires hasLeavesIndexedFrom(r, i)
        requires |p| == height(r)
        requires nodeAt(p, r) == leavesIn(r)[k]

        requires 0 <= i < |p|
        // ensures p[i] == 0 ==> siblingAt(take(p, i + 1), r).v == zeroes[i]
    {
        if height(r) == 0 {
           //   Thanks Dafny
        } else {
            //  |p| >= 1, induction on left and right child
            //  Prove pre-conditions hold for them
            if first(p) == 0 {
                //  induction on left child. Prove 
                // assume(p[i] == 0 ==> siblingAt(take(p, i + 1), r).v == zeroes[i]);
            } else {
                //  assume(p[i] == 0 ==> siblingAt(take(p, i + 1), r).v == zeroes[i]);
            }
           
        }
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
        requires nodeAt(p, r) == leavesIn(r)[k]    
        requires nodeAt(p, r') == leavesIn(r')[k]

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
 }