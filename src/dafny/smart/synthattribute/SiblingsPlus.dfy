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

/**
 *  Helper lemma to prove property on siblings.
 */
module SiblingsPlus {
 
    import opened CompleteTrees
    import opened Helpers
    import opened PathInCompleteTrees
    import opened SeqOfBits
    import opened SeqHelpers
    import opened Trees

    /**
     *  This is the base case for the proof of Lemma [[LeftSiblings.]]
     *  Let two trees r and r' (same height) that agree on all values of their leaves 
     *  except possibly at k.
     *  Let p be the path to the k-th leaf.
     *  Then the values on the i-th left siblings of p in r is equal to the values on 
     *  the i-th left siblings of p in r'.
     *
     *  @param  p       A path to a leaf.
     *  @param  r       A tree.
     *  @param  r'      A tree.
     *  @param  k       The index of a leaf in r and r'.
     *  @param  f       The synthesised attribute to decorate the trees.
     *  @param  index   The initial value of the indexing of leaves in r and r'.
     */
     lemma {:induction p} siblingsInEquivTreesBaseCase<T>(p : seq<bit>, r : Tree<T>, r' : Tree<T>, k: nat, f : (T, T) -> T, index: nat) 

        requires isCompleteTree(r) && isCompleteTree(r')
        requires isDecoratedWith(f, r) && isDecoratedWith(f, r')
        requires height(r) == height(r') >= 1
        requires hasLeavesIndexedFrom(r, index) && hasLeavesIndexedFrom(r', index)

        requires k < |leavesIn(r)| == |leavesIn(r')|
        requires takeLeavesIn(r, k) == takeLeavesIn(r', k)
        requires dropLeavesIn(r, k + 1) == dropLeavesIn(r', k + 1)

        requires 1 <= |p| == height(r)
        requires bitListToNat(p) == k 
 
        ensures siblingValueAt(p, r, 1) == siblingValueAt(p, r', 1)
    {
        reveal_takeLeavesIn();
        reveal_dropLeavesIn();
        reveal_siblingValueAt();

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
                initPathDeterminesIndex(r, p, k, index);
                assert(k < power2(height(r)) / 2);
                var k' := power2(height(r)) / 2;
                assert(k < k');
                assert(|leavesIn(lc)| == |leavesIn(lc')| == k');
                assert(k < |leavesIn(lc)| == |leavesIn(lc')|);

                calc == {
                    siblingAt(take(p, 1), r).v;
                    calc == {
                        take(p, 1);
                        p[..1];
                        [p[0]];
                        [0];
                    }
                    siblingAt([0], r).v;
                    nodeAt([] + [1], r).v;
                    calc == {
                        [] + [1];
                        [1];
                    }
                    nodeAt([1], r).v;
                    rc.v;
                    { sameLeavesSameRoot(rc, rc', f, index + k') ; }
                    rc'.v;
                    nodeAt([1], r').v;
                    calc == {
                        [] + [1];
                        [1];
                    }
                    nodeAt([] + [1], r').v;
                    siblingAt([0], r').v;
                    calc == {
                        take(p, 1);
                        p[..1];
                        [p[0]];
                        [0];
                    }
                    siblingAt(take(p, 1), r').v;
                }
             } else {
                assert(first(p) == p[0] == 1);
                var k' := power2(height(r)) / 2;
                assert(k >= k');
                calc == {
                    siblingAt(take(p, 1), r).v;
                    calc == {
                        take(p, 1);
                        p[..1];
                        [p[0]];
                        [1];
                    }
                    siblingAt([1], r).v;
                    nodeAt([] + [0], r).v;
                    calc == {
                        [] + [0];
                        [0];
                    }
                    nodeAt([0], r).v;
                    lc.v;
                    { 
                        calc == {
                            leavesIn(lc);
                            leavesIn(r)[..k'];
                            take(leavesIn(r), k');
                            { 
                                assert(k >= k'); 
                                assert(take(leavesIn(r), k) == take(leavesIn(r'), k)); 
                                prefixSeqs(leavesIn(r), leavesIn(r'), k', k);
                            }
                            take(leavesIn(r'), k');
                            leavesIn(r')[..k'];
                            leavesIn(lc');
                        }
                        sameLeavesSameRoot(lc, lc', f, index) ; 
                    }
                    lc'.v;
                    nodeAt([0], r').v;
                    calc == {
                        [] + [0];
                        [0] ;
                    }
                    nodeAt([] + [0], r').v;
                    siblingAt([1], r').v;
                    calc == {
                        take(p, 1);
                        p[..1];
                        [p[0]];
                        [1];
                    }
                    siblingAt(take(p, 1), r').v;
                }
             }
        }
    }

    /**
     *  This is the prelimiary of inductive case for the proof of Lemma 
     *  [[LeftSiblings.leftSiblingsInEquivTrees]]
     *  It establishes the pre-conditions to apply apply the lemma 
     *  [[LeftSiblings.leftSiblingsInEquivTrees]]
     *  on the left child.
     *
     *  @param  p       A path to a leaf.
     *  @param  r       A tree.
     *  @param  r'      A tree.
     *  @param  k       The index of a leaf in r and r'.
     *  @param  f       The synthesised attribute to decorate the trees.
     *  @param  i       An index on the path p.
     *  @param  index   The initial value of the indexing of leaves in r and r'.
     */
    lemma {:induction false } {:timeLimitMultiplier 2} siblingsInEquivTreesNonBaseCaseFirstLeft<T>(p : seq<bit>, r : Tree<T>, r' : Tree<T>, k: nat, f : (T, T) -> T, i : nat, index: nat) 

        requires isCompleteTree(r)
        requires isCompleteTree(r')
        requires isDecoratedWith(f, r)
        requires isDecoratedWith(f, r')
        requires height(r) == height(r') >= 1
        requires hasLeavesIndexedFrom(r, index)
        requires hasLeavesIndexedFrom(r', index)

        requires k < |leavesIn(r)| == |leavesIn(r')|
        requires takeLeavesIn(r, k) == takeLeavesIn(r', k)
        requires dropLeavesIn(r, k + 1) == dropLeavesIn(r', k + 1)

        requires 1 <= |p| == height(r)
        requires bitListToNat(p) == k
       
        requires 2 <= i + 1 <= |p| == height(r) 
        requires first(p) == 0
        
        ensures match (r, r') 
            case (Node(_, lc, rc), Node(_, lc', rc')) => 
                k < power2(height(r)) / 2
                && k < |leavesIn(lc)| == |leavesIn(lc')|
                && takeLeavesIn(lc, k) == takeLeavesIn(lc', k)
                && dropLeavesIn(lc, k + 1) == dropLeavesIn(lc', k + 1)
                && nodeAt(tail(p), lc) == leavesIn(lc)[k]
                && leavesIn(lc')[k] == nodeAt(tail(p), lc')
                && siblingValueAt(p, r', i + 1) == siblingValueAt(tail(p), lc', i)
                && siblingValueAt(p, r, i + 1) == siblingValueAt(tail(p), lc, i)
    {
        reveal_siblingValueAt();
        reveal_takeLeavesIn();
        reveal_dropLeavesIn();

        match (r, r')
                case (Node(_, lc, rc), Node(_, lc', rc')) =>
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
                
                //  Prove some properties that guarantee pre-conditions of
                //  functions/lemmas called in the proof.
                completeTreeNumberLemmas(r);
                assert(power2(height(r)) == |leavesIn(r)|);
                initPathDeterminesIndex(r, p, k, index);
                assert(k < power2(height(r)) / 2);
                var k' :=  power2(height(r)) / 2;
                assert(k < k');
                assert(|leavesIn(lc)| == |leavesIn(lc')| == power2(height(r)) / 2 == k');
                assert(k < |leavesIn(lc)| == |leavesIn(lc')|);

                assert(1 <= i + 1 <= |p|);

                calc == {
                    first(take(p,i + 1));
                    first(p);
                    0;
                }

                //    siblingAt(take(p,i + 1), r).v is the same as siblingAt(take(tail(p), i), lc).v;
                calc == {
                    siblingValueAt(p, r, i + 1);
                    siblingAt(take(p,i + 1), r).v;
                    { assert(first(p) == 0) ; simplifySiblingAtIndexFirstBit(p, r, i + 1); }
                    siblingAt(take(tail(p), i), lc).v;
                    siblingValueAt(tail(p), lc, i);
                }

                calc == {
                    take(leavesIn(lc), k);
                    take(leavesIn(r)[..k'], k);
                    take(take(leavesIn(r), k'), k);
                    { seqTakeTake(leavesIn(r), k, k'); }
                    take(leavesIn(r), k);
                    takeLeavesIn(r, k);
                    takeLeavesIn(r', k);
                    take(leavesIn(r'), k);
                    { seqTakeTake(leavesIn(r'), k, k'); }
                    take(take(leavesIn(r'), k), k);
                    take(leavesIn(lc'), k);
                }

                assert(k + 1 <=  k');
                calc == {
                    drop(leavesIn(lc), k  + 1);
                    drop(take(leavesIn(r), k'), k  + 1);
                    { 
                        seqDropTake(leavesIn(r), k + 1, k'); 
                    }
                    leavesIn(r)[k + 1 .. k'];
                    { suffixSeqs(leavesIn(r), leavesIn(r'), k + 1, k'); } 
                    leavesIn(r')[k + 1 .. k'];
                    { 
                        seqDropTake(leavesIn(r'), k + 1, k'); 
                    }
                    drop(take(leavesIn(r'), k'), k + 1);
                    leavesIn(r')[..k'][k + 1..];
                    drop(leavesIn(lc'), k + 1);
                }

                calc == {
                    leavesIn(lc)[k];
                    leavesIn(r)[k];
                    nodeAt(p, r);
                    { simplifyNodeAtFirstBit(p, r); }
                    nodeAt(tail(p), lc);
                }

                calc == {
                    leavesIn(lc')[k];
                    leavesIn(r')[k];
                    nodeAt(p, r');
                    { simplifyNodeAtFirstBit(p, r'); }
                    nodeAt(tail(p), lc');
                }

                calc == {
                    siblingAt(take(p,i + 1), r').v;
                    { simplifySiblingAtIndexFirstBit(p, r', i + 1); }
                    siblingAt(take(tail(p), i), lc').v;

                }
    }

    /**
     *  This is the preliminary of inductive case for the proof of Lemma
     *  [[LeftSiblings.leftSiblingsInEquivTrees]]
     *  It establishes the pre-conditions to apply apply the lemma 
     *  [[LeftSiblings.leftSiblingsInEquivTrees]]
     *  on the right child.
     *
     *  @param  p       A path to a leaf.
     *  @param  r       A tree.
     *  @param  r'      A tree.
     *  @param  k       The index of a leaf in r and r'.
     *  @param  f       The synthesised attribute to decorate the trees.
     *  @param  i       An index on the path p.
     *  @param  index   The initial value of the indexing of leaves in r and r'.
     */
    lemma {:induction false} {:timeLimitMultiplier 2} siblingsInEquivTreesNonBaseCaseFirstRight<T>(p : seq<bit>, r : Tree<T>, r' : Tree<T>, k: nat, f : (T, T) -> T, i : nat, index: nat) 
        requires isCompleteTree(r)
        requires isCompleteTree(r')
        requires isDecoratedWith(f, r)
        requires isDecoratedWith(f, r')
        requires height(r) == height(r') >= 1
        requires hasLeavesIndexedFrom(r, index)
        requires hasLeavesIndexedFrom(r', index)

        requires k < |leavesIn(r)| == |leavesIn(r')|
       
        requires takeLeavesIn(r, k) == takeLeavesIn(r', k)
        requires dropLeavesIn(r, k + 1) == dropLeavesIn(r', k + 1)

        requires power2(height(r)) / 2  <= k < |leavesIn(r)| == |leavesIn(r')|
        requires 2 <= i + 1 <= |p| == height(r) 
        requires first(p) == 1

        requires bitListToNat(p) == k

        ensures match (r, r') 
            case (Node(_, lc, rc), Node(_, lc', rc')) => 
                var k' := k  - power2(height(r)) / 2;
                k >= power2(height(r)) / 2
                && 0 <= k - power2(height(r)) / 2  < |leavesIn(rc)| == |leavesIn(rc')|
                && takeLeavesIn(rc, k') == takeLeavesIn(rc', k')
                && dropLeavesIn(rc, k' + 1) == dropLeavesIn(rc', k' + 1)
                && nodeAt(tail(p), rc) == leavesIn(rc)[k']
                && nodeAt(tail(p), rc') == leavesIn(rc')[k']
                && siblingValueAt(p, r, i + 1) == siblingValueAt(tail(p), rc, i)
                && siblingValueAt(p, r', i + 1) == siblingValueAt(tail(p), rc', i)

    {
        reveal_siblingValueAt();
        reveal_takeLeavesIn();
        reveal_dropLeavesIn();

        match (r, r')
            case (Node(_, lc, rc), Node(_, lc', rc')) =>
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

            //  Use vars to store power2(height(r)) / 2 and prove some useful inequalities.
            var k'' := power2(height(r)) / 2;
            initPathDeterminesIndex(r, p, k, index);
            assert(k >= power2(height(r)) / 2 == k'');
            var k' := k  - power2(height(r)) / 2;
            assert(k + 1 >  k'');
            assert(first(take(p,i + 1)) == first(p));
        
            calc == {
                leavesIn(rc)[k'];
                { childrenInCompTreesHaveHalfNumberOfLeaves(r, height(r));}
                leavesIn(r)[k];
                { leafAtPathIsIntValueOfPath(p, r, k, index) ;}
                nodeAt(p, r);
                { simplifyNodeAtFirstBit(p, r); } 
                nodeAt(tail(p),  rc);
            }
            calc == {
                leavesIn(rc')[k'];
                { childrenInCompTreesHaveHalfNumberOfLeaves(r', height(r'));}
                leavesIn(r')[k];
                { leafAtPathIsIntValueOfPath(p, r', k, index) ;}
                nodeAt(p, r');
                { simplifyNodeAtFirstBit(p, r'); } 
                nodeAt(tail(p),  rc');
            }
            simplifySiblingAtIndexFirstBit(p, r', i + 1);
            simplifySiblingAtIndexFirstBit(p, r, i + 1);

    }

    /**
     *  If two trees are decorated with same synthesised attribute f ans have same values on leaves,
     *  they have same values on their roots.
     *  @param  r       A tree.
     *  @param  r'      A tree.
     *  @param  f       The synthesised attribute to decorate the trees.
     *  
     */
    lemma {:induction r, r'} sameLeavesSameRoot<T>(r : Tree<T>, r' : Tree<T>, f : (T, T) -> T, index : nat) 

        requires isCompleteTree(r)
        requires isCompleteTree(r')
        requires isDecoratedWith(f, r)
        requires isDecoratedWith(f, r')
        requires height(r) == height(r') >= 0
        requires hasLeavesIndexedFrom(r, index)
        requires hasLeavesIndexedFrom(r', index)
        requires leavesIn(r) == leavesIn(r')

        ensures r.v == r'.v

        decreases r 

        {
            if height(r) == 0 {
                //  Thanks Dafny
            } else {
                //  Induction on lc and rc and combine root with f
                match (r, r') 
                    case (Node(_, lc, rc), Node(_, lc', rc')) => 
                        //  Check pre-conditions on lc rc before induction
                        childrenInCompTreesHaveHeightMinusOne(r);
                        childrenInCompTreesHaveHeightMinusOne(r');
                        childrenCompTreeValidIndex(r, height(r), index);
                        childrenCompTreeValidIndex(r', height(r'), index);
                        completeTreeNumberLemmas(r);
                        completeTreeNumberLemmas(r');
                        childrenInCompTreesHaveHalfNumberOfLeaves(r, height(r));
                        childrenInCompTreesHaveHalfNumberOfLeaves(r', height(r'));

                        calc == {
                            r.v;
                            f(lc.v, rc.v);
                            { sameLeavesSameRoot(lc, lc', f, index); }
                            f(lc'.v, rc.v);
                            { sameLeavesSameRoot(rc, rc', f, index + power2(height(r)) / 2); }
                            f(lc'.v, rc'.v);
                            r'.v;
                        }
            }
        }
 }