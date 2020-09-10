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
include "../synthattribute/GenericComputation.dfy"
include "../helpers/Helpers.dfy"
include "../MerkleTrees.dfy"
include "../paths/NextPathInCompleteTreesLemmas.dfy"
include "../paths/PathInCompleteTrees.dfy"
include "../seqofbits/SeqOfBits.dfy"
include "../helpers/SeqHelpers.dfy"
include "../trees/Trees.dfy"

/**
 *  Hekoer lemma to prove property on siblings.
 */
module LeftSiblingsPlus {
 
    import opened DiffTree
    import opened CompleteTrees
    import opened GenericComputation
    import opened Helpers
    import opened MerkleTrees
    import opened NextPathInCompleteTreesLemmas
    import opened PathInCompleteTrees
    import opened SeqOfBits
    import opened SeqHelpers
    import opened Trees

    /**
     *  In a decorated tree, 
     *  The values on the siblings of a path do not depend on the value at the end of the path.
     */
     lemma testLemmaBaseCase<T>(p : seq<bit>, r : Tree<T>, r' : Tree<T>, k: nat, f : (T, T) -> T, index: nat) 

        requires isCompleteTree(r)
        requires isCompleteTree(r')
        /** `r` is decorated with attribute `f`. */
        requires isDecoratedWith(f, r)
        requires isDecoratedWith(f, r')

        requires height(r) == height(r') >= 2

        requires hasLeavesIndexedFrom(r, index)
        requires hasLeavesIndexedFrom(r', index)

        /**  all leaves after the k leaf are zero. */
        requires k < |leavesIn(r)| == |leavesIn(r')|
        requires 1 <= |p| == height(r) - 1

        requires leavesIn(r)[..k] == leavesIn(r')[..k]
        requires leavesIn(r)[k + 1..] == leavesIn(r')[k + 1..]

        requires nodeAt(p, r) == leavesIn(r)[k]    
        requires nodeAt(p, r') == leavesIn(r')[k]

        ensures siblingAt(take(p, 1), r).v == siblingAt(take(p, 1), r').v

    {
        match (r, r')
                case (Node(_, lc, rc), Node(_, lc', rc')) =>
                //  Prove some properties that guarantee pre-conditions of
                //  functions/lemmas called in the proof.
                completeTreeNumberLemmas(r);
                assert(power2(height(r) - 1) == |leavesIn(r)|);


        if |p| == 1 {

        } else {
            childrenCompTreeValidIndex(r, height(r), index);
            childrenCompTreeValidIndex(r', height(r'), index);

            childrenInCompTreesHaveHalfNumberOfLeaves(r, height(r));
            childrenInCompTreesHaveHalfNumberOfLeaves(r', height(r'));

            completeTreeNumberLemmas(r);
            completeTreeNumberLemmas(r');

             if first(p) == 0 {
                initPathDeterminesIndex(r, p, k, index);
                assert(k < power2(height(r) - 1) / 2);
                assert(|leavesIn(lc)| == |leavesIn(lc')| == power2(height(r) - 1) / 2);
                assert(k < |leavesIn(lc)| == |leavesIn(lc')|);

                calc == {
                    [] + [1];
                    [1];
                }
                calc == {
                    siblingAt(take(p, 1), r).v;
                    calc == {
                        take(p, 1);
                        p[..1];
                        [p[0]];
                    }
                    siblingAt([p[0]], r).v;
                    siblingAt([0], r).v;
                    nodeAt([] + [1], r).v;
                    calc == {
                        [] + [1];
                        [1];
                    }
                    nodeAt([1], r).v;
                    rc.v;
                    { 
                        assert(leavesIn(rc) == leavesIn(rc')); 
                        assert(hasLeavesIndexedFrom(rc,  index + power2(height(r) - 1) / 2));
                        assert(hasLeavesIndexedFrom(rc',  index + power2(height(r) - 1) / 2));
                        assert(isCompleteTree(r));
                        assert(isCompleteTree(r'));
                        assert(isDecoratedWith(f, r));
                        assert(isDecoratedWith(f, r'));
                        sameLeavesSameRoot(rc, rc', f, index + power2(height(r) - 1) / 2) ; 
                    }
                    rc'.v;
                    nodeAt([1], r').v;
                    nodeAt([] + [1], r').v;
                    siblingAt([0], r').v;
                    siblingAt([p[0]], r').v;
                    siblingAt(take(p, 1), r').v;
                }
             } else {
                 
                calc == {
                    [] + [0];
                    [0];
                }
                calc == {
                    siblingAt(take(p, 1), r).v;
                    calc == {
                        take(p, 1);
                        p[..1];
                        [p[0]];
                    }
                    siblingAt([p[0]], r).v;
                    siblingAt([1], r).v;
                    nodeAt([] + [0], r).v;
                    nodeAt([0], r).v;
                    lc.v;
                    { 
                    calc == {
                        leavesIn(lc);
                        leavesIn(r)[..power2(height(r) - 1) / 2];
                        { 
                            assert(k >= power2(height(r) - 1) / 2); 
                            assert(leavesIn(r)[..k] == leavesIn(r')[..k]); 
                            prefixSeqs(leavesIn(r), leavesIn(r'), power2(height(r) - 1) / 2, k);
                        }
                        leavesIn(r')[..power2(height(r) - 1) / 2];
                        leavesIn(lc');
                    }
                    assert(leavesIn(lc) == leavesIn(lc')); 
                    assert(hasLeavesIndexedFrom(lc,  index));
                    assert(hasLeavesIndexedFrom(lc',  index));
                    assert(isCompleteTree(r));
                    assert(isCompleteTree(r));
                    assert(isDecoratedWith(f, r));
                    assert(isDecoratedWith(f, r'));
                    sameLeavesSameRoot(lc, lc', f, index) ; 
                        }
                        lc'.v;
                        nodeAt([0], r').v;
                        nodeAt([] + [0], r').v;
                        siblingAt([1], r').v;
                        siblingAt([p[0]], r').v;
                        siblingAt(take(p, 1), r').v;
                        }
             }
        }
    }

    lemma testLemmaNonBaseCaseFirstLeft<T>(p : seq<bit>, r : Tree<T>, r' : Tree<T>, k: nat, f : (T, T) -> T, i : nat, index: nat) 
        // requires i == 0

        requires isCompleteTree(r)
        requires isCompleteTree(r')
        /** `r` is decorated with attribute `f`. */
        requires isDecoratedWith(f, r)
        requires isDecoratedWith(f, r')

        requires height(r) == height(r') >= 2

        requires hasLeavesIndexedFrom(r, index)
        requires hasLeavesIndexedFrom(r', index)

        /**  all leaves after the k leaf are zero. */
        requires k < |leavesIn(r)| == |leavesIn(r')|
        requires 2 <= i + 1 <= |p| == height(r) - 1

        requires leavesIn(r)[..k] == leavesIn(r')[..k]
        requires leavesIn(r)[k + 1..] == leavesIn(r')[k + 1..]

        requires nodeAt(p, r) == leavesIn(r)[k]    
        requires nodeAt(p, r') == leavesIn(r')[k]

        requires first(p) == 0
        // requires 0 <= i < |p|
        
        // ensures k < power2(height(r) - 1) / 2
        ensures match (r, r') 
            case (Node(_, lc, rc), Node(_, lc', rc')) => 
                k < power2(height(r) - 1) / 2
                && k < |leavesIn(lc)| == |leavesIn(lc')|
                && leavesIn(lc)[..k] == leavesIn(lc')[..k]
                && leavesIn(lc)[k + 1..] == leavesIn(lc')[k + 1..]
                && nodeAt(tail(p), lc) == leavesIn(lc)[k]
                && leavesIn(lc')[k] == nodeAt(tail(p), lc')
                && isDecoratedWith(f, lc)
                && isDecoratedWith(f, lc')
                && siblingAt(take(p,i + 1), r').v == siblingAt(take(tail(p), i), lc').v
                && siblingAt(take(p,i + 1), r).v == siblingAt(take(tail(p), i), lc).v

        // siblingAt(take(p, 1), r).v == siblingAt(take(p, 1), r').v
    {
        match (r, r')
                case (Node(_, lc, rc), Node(_, lc', rc')) =>
                childrenCompTreeValidIndex(r, height(r), index);
                childrenCompTreeValidIndex(r', height(r'), index);

                childrenInCompTreesHaveHalfNumberOfLeaves(r, height(r));
                childrenInCompTreesHaveHalfNumberOfLeaves(r', height(r'));

                completeTreeNumberLemmas(r);
                completeTreeNumberLemmas(r');

                //  Prove some properties that guarantee pre-conditions of
                //  functions/lemmas called in the proof.
                completeTreeNumberLemmas(r);
                assert(power2(height(r) - 1) == |leavesIn(r)|);
                initPathDeterminesIndex(r, p, k, index);
                assert(k < power2(height(r) - 1) / 2);
                // assert(r.Node?);
                // childrenInCompTreesHaveSameNumberOfLeaves(r);
                // childrenInCompTreesHaveSameNumberOfLeaves(r');
                assert(|leavesIn(lc)| == |leavesIn(lc')| == power2(height(r) - 1) / 2);
                assert(k < |leavesIn(lc)| == |leavesIn(lc')|);

                assert(1 <= i + 1 <= |p|);
                calc {
                    first(take(p,i + 1));
                    { seqIndexLemmas(p, i + 1) ; }
                    first(p);
                    0;
                }
                //    siblingAt(take(p,i + 1), r).v is the same as siblingAt(take(tail(p), i), lc).v;
                calc == {
                    siblingAt(take(p,i + 1), r).v;
                    // { simplifySiblingAtFirstBit(take(p,i + 1), r) ; }
                    // siblingAt(tail(take(p,i + 1)), lc).v;
                    // { seqIndexLemmas(p, i + 1); }
                    { assert(first(p) == 0) ; simplifySiblingAtIndexFirstBit(p, r, i + 1); }
                    siblingAt(take(tail(p), i), lc).v;
                }
                assert(siblingAt(take(p,i + 1), r).v == siblingAt(take(tail(p), i), lc).v); 
                    calc == {
                    leavesIn(lc)[..k];
                    leavesIn(r)[..power2(height(r) - 1) / 2][..k];
                    { seqTakeTake(leavesIn(r), k, power2(height(r) - 1) / 2); }
                    leavesIn(r)[..k];
                    leavesIn(r')[..k];
                    { seqTakeTake(leavesIn(r'), k, power2(height(r) - 1) / 2); }
                    leavesIn(r')[..power2(height(r) - 1) / 2][..k];
                    leavesIn(lc')[..k];
                }
                assert(leavesIn(lc)[..k] == leavesIn(lc')[..k]);
                assert(k + 1 <=  power2(height(r) - 1) / 2);
                calc == {
                    leavesIn(lc)[k  + 1..];
                    leavesIn(r)[..power2(height(r) - 1) / 2][k + 1 ..];
                    { 
                        seqDropTake(leavesIn(r), k + 1, power2(height(r) - 1) / 2); 
                    }
                    leavesIn(r)[k + 1 .. power2(height(r) - 1) / 2];
                    { suffixSeqs(leavesIn(r), leavesIn(r'), k + 1, power2(height(r) - 1) / 2); } 
                    leavesIn(r')[k + 1 .. power2(height(r) - 1) / 2];
                    { 
                        seqDropTake(leavesIn(r'), k + 1, power2(height(r) - 1) / 2); 
                    }
                    leavesIn(r')[..power2(height(r) - 1) / 2][k + 1..];
                    leavesIn(lc')[k + 1..];
                }

                assert(leavesIn(lc)[k + 1..] == leavesIn(lc')[k + 1..]);

                    calc == {
                    leavesIn(lc)[k];
                    leavesIn(r)[k];
                    nodeAt(p, r);
                    { simplifyNodeAtFirstBit(p, r); }
                    nodeAt(tail(p), lc);
                }
                assert(nodeAt(tail(p), lc) == leavesIn(lc)[k]);

                calc == {
                    leavesIn(lc')[k];
                    leavesIn(r')[k];
                    nodeAt(p, r');
                    { simplifyNodeAtFirstBit(p, r'); }
                    nodeAt(tail(p), lc');
                }
                assert(leavesIn(lc')[k] == nodeAt(tail(p), lc'));

                 //    siblingAt(take(p,i + 1), r').v is the same as siblingAt(take(tail(p), i), lc').v;
                        calc == {
                            siblingAt(take(p,i + 1), r').v;
                            // { simplifySiblingAtFirstBit(take(p,i + 1), r') ; }
                            // siblingAt(tail(take(p,i + 1)), lc').v;
                            // { seqIndexLemmas(p, i + 1); }
                            { simplifySiblingAtIndexFirstBit(p, r', i + 1); }
                            siblingAt(take(tail(p), i), lc').v;
                        }
                        assert(siblingAt(take(p,i + 1), r').v == siblingAt(take(tail(p), i), lc').v);



    }

    lemma testLemmaNonBaseCaseFirstRight<T>(p : seq<bit>, r : Tree<T>, r' : Tree<T>, k: nat, f : (T, T) -> T, i : nat, index: nat) 
        // requires i == 0

        requires isCompleteTree(r)
        requires isCompleteTree(r')
        /** `r` is decorated with attribute `f`. */
        requires isDecoratedWith(f, r)
        requires isDecoratedWith(f, r')

        requires height(r) == height(r') >= 2

        requires hasLeavesIndexedFrom(r, index)
        requires hasLeavesIndexedFrom(r', index)

        /**  all leaves after the k leaf are zero. */
        requires power2(height(r) - 1) / 2  <= k < |leavesIn(r)| == |leavesIn(r')|
        requires 2 <= i + 1 <= |p| == height(r) - 1

        requires leavesIn(r)[..k] == leavesIn(r')[..k]
        requires leavesIn(r)[k + 1..] == leavesIn(r')[k + 1..]

        requires nodeAt(p, r) == leavesIn(r)[k]    
        requires nodeAt(p, r') == leavesIn(r')[k]

        requires first(p) == 1
        // requires 0 <= i < |p|
        
        // ensures k < power2(height(r) - 1) / 2
        ensures match (r, r') 
            case (Node(_, lc, rc), Node(_, lc', rc')) => 
                var k' := k  - power2(height(r) - 1) / 2;
                k >= power2(height(r) - 1) / 2
                && 0 <= k - power2(height(r) - 1) / 2  < |leavesIn(rc)| == |leavesIn(rc')|
                && leavesIn(rc)[..k'] ==  leavesIn(rc')[.. k']
                && leavesIn(rc)[k' + 1..] ==  leavesIn(rc')[k' +  1..]
                && nodeAt(tail(p), rc) == leavesIn(rc)[k']
                && nodeAt(tail(p), rc') == leavesIn(rc')[k']
                && isDecoratedWith(f, lc)
                && isDecoratedWith(f, lc')
                && siblingAt(take(p,i + 1), r').v == siblingAt(take(tail(p), i), rc').v
                && siblingAt(take(p,i + 1), r).v == siblingAt(take(tail(p), i), rc).v

    {
            match (r, r')
                case (Node(_, lc, rc), Node(_, lc', rc')) =>
                childrenCompTreeValidIndex(r, height(r), index);
                childrenCompTreeValidIndex(r', height(r'), index);

                childrenInCompTreesHaveHalfNumberOfLeaves(r, height(r));
                childrenInCompTreesHaveHalfNumberOfLeaves(r', height(r'));

                completeTreeNumberLemmas(r);
                completeTreeNumberLemmas(r');

                initPathDeterminesIndex(r, p, k, index);
                assert(k >= power2(height(r) - 1) / 2);
                // assert(|leavesIn(rc)| == |leavesIn(rc')| == power2(height(r) - 1) / 2);
                // assert(|leavesIn(lc)| == |leavesIn(lc')| == power2(height(r) - 1) / 2);

                calc {
                    first(take(p,i + 1));
                    { seqIndexLemmas(p, i + 1) ; }
                    first(p);
                    1;
                }
                   //  this var k' and the assert 
                // (although not used) for some reason computing them speeds up the provers' time ...
                var k' := k  - power2(height(r) - 1) / 2;
                assert(k + 1 >  power2(height(r) - 1) / 2);

                //    siblingAt(take(p,i + 1), r).v is the same as siblingAt(take(tail(p), i), lc).v;
                calc == {
                    siblingAt(take(p,i + 1), r).v;
                    // { simplifySiblingAtFirstBit(take(p,i + 1), r) ; }
                    // siblingAt(tail(take(p,i + 1)), rc).v;
                    // { seqIndexLemmas(p, i + 1); }
                    { simplifySiblingAtIndexFirstBit(p, r, i + 1); }
                    siblingAt(take(tail(p), i), rc).v;
                }
                // simplifySiblingAtIndexFirstBit(p, r, i + 1);
                assert(siblingAt(take(p,i + 1), r).v == siblingAt(take(tail(p), i), rc).v);


                calc == {
                    leavesIn(rc)[..k'];
                    leavesIn(r)[power2(height(r) - 1) / 2..][..k'];
                    {
                        seqTakeDrop(leavesIn(r), power2(height(r) - 1) / 2, k);
                    }
                    leavesIn(r)[power2(height(r) - 1) / 2..k];
                    {
                        prefixSeqs(leavesIn(r), leavesIn(r'), power2(height(r) - 1) / 2, k);
                    }

                    leavesIn(r')[power2(height(r) - 1) / 2..k];
                    {
                        seqTakeDrop(leavesIn(r'), power2(height(r) - 1) / 2, k);
                    }
                    leavesIn(r')[power2(height(r) - 1) / 2..][..k'];
                    leavesIn(rc')[.. k'];
                }
                assert(leavesIn(rc)[..k'] == leavesIn(rc')[..k']);

                calc == {
                    leavesIn(rc)[k' + 1..];
                    leavesIn(r)[power2(height(r) - 1) / 2..][k' + 1 ..]; 
                    { 
                        seqDropDrop(leavesIn(r), power2(height(r) - 1) / 2, k + 1); 
                    }
                    leavesIn(r)[k + 1..];
                    leavesIn(r')[k + 1 ..];
                    { 
                        seqDropDrop(leavesIn(r'), power2(height(r) - 1) / 2, k + 1); 
                    }
                    leavesIn(r')[power2(height(r) - 1) / 2..][k' + 1 ..]; 
                    leavesIn(rc')[k' + 1..];
                }
                assert(leavesIn(rc)[k' + 1..] == leavesIn(rc')[k' + 1..]);

                calc == {
                    leavesIn(rc)[k'];
                    leavesIn(r)[k];
                    nodeAt(p, r);
                    { simplifyNodeAtFirstBit(p, r); }
                    nodeAt(tail(p), rc);
                }
                assert(nodeAt(tail(p), rc) == leavesIn(rc)[k']);

                calc == {
                    leavesIn(rc')[k'];
                    leavesIn(r')[k];
                    nodeAt(p, r');
                    { simplifyNodeAtFirstBit(p, r'); }
                    nodeAt(tail(p), rc');
                }
                assert(nodeAt(tail(p), rc') == leavesIn(rc')[k']);

                calc == {
                    siblingAt(take(p,i + 1), r').v;
                    // { simplifySiblingAtFirstBit(take(p,i + 1), r') ; }
                    // siblingAt(tail(take(p,i + 1)), rc').v;
                    // { seqIndexLemmas(p, i + 1); }
                    {  assert(first(p) == 1); simplifySiblingAtIndexFirstBit(p, r', i + 1);}
                    siblingAt(take(tail(p), i), rc').v;
                }
                // simplifySiblingAtIndexFirstBit(p, r', i + 1);
                assert(siblingAt(take(p,i + 1), r').v == siblingAt(take(tail(p), i), rc').v); 

    }

    /**
     *  
     *  @todo This is a version of testLemma that is supposed to be more modular.
     *  However, the curren tone seems to work OK (<= 10sec to verify) so
     *  it is left as a WIP.
     */
    lemma {:induction p, r, r', i} testLemmav2<T>(p : seq<bit>, r : Tree<T>, r' : Tree<T>, f :(T, T) -> T, k: nat, i: nat, index: nat)
        requires isCompleteTree(r)
        requires isCompleteTree(r')
        /** `r` is decorated with attribute `f`. */
        requires isDecoratedWith(f, r)
        requires isDecoratedWith(f, r')

        requires height(r) == height(r') >= 2

        requires hasLeavesIndexedFrom(r, index)
        requires hasLeavesIndexedFrom(r', index)

        /**  all leaves after the k leaf are zero. */
        requires k < |leavesIn(r)| == |leavesIn(r')|
        requires 1 <= |p| == height(r) - 1

        requires leavesIn(r)[..k] == leavesIn(r')[..k]
        requires leavesIn(r)[k + 1..] == leavesIn(r')[k + 1..]

        requires nodeAt(p, r) == leavesIn(r)[k]    
        requires nodeAt(p, r') == leavesIn(r')[k]

        requires 0 <= i < |p|
        ensures siblingAt(take(p, i + 1), r).v == siblingAt(take(p, i + 1), r').v

    {
        if |p| == 1 {
            //  Thanks Dafny
        } else {
            if i == 0 {
                testLemmaBaseCase(p, r, r', k, f, index);
            } else {
                assert(r.Node?);
                assert(r'.Node?);
                childrenInCompTreesHaveSameNumberOfLeaves(r);
                childrenInCompTreesHaveSameNumberOfLeaves(r');
                childrenCompTreeValidIndex(r, height(r), index);
                childrenCompTreeValidIndex(r', height(r'), index);

                childrenInCompTreesHaveHalfNumberOfLeaves(r, height(r));
                childrenInCompTreesHaveHalfNumberOfLeaves(r', height(r'));

                completeTreeNumberLemmas(r);
                completeTreeNumberLemmas(r');

                //  |p| >=1, i >= 1, induction on child depending on first(p)
                if (first(p) == 0) {
                    initPathDeterminesIndex(r, p, k, index);
                    assert(k < power2(height(r) - 1) / 2);
                    // assert(r.Node?);
                    // childrenInCompTreesHaveSameNumberOfLeaves(r);
                    // childrenInCompTreesHaveSameNumberOfLeaves(r');
                    assert(|leavesIn(r.left)| == |leavesIn(r'.left)| == power2(height(r) - 1) / 2);
                    assert(k < |leavesIn(r.left)| == |leavesIn(r'.left)|);

                    assume(
                     siblingAt(take(p, i + 1), r).v == siblingAt(take(p, i + 1), r').v
                );
                } else {
                    assume(
                     siblingAt(take(p, i + 1), r).v == siblingAt(take(p, i + 1), r').v
                );
                }
            }
        }
        
    }

    lemma sameLeavesSameRoot<T>(r : Tree<T>, r2 : Tree<T>, f : (T, T) -> T, index : nat) 
        requires isCompleteTree(r)
        requires isCompleteTree(r2)
        /** `r` is decorated with attribute `f`. */
        requires isDecoratedWith(f, r)
        requires isDecoratedWith(f, r2)

        requires height(r) == height(r2) >= 1

        requires hasLeavesIndexedFrom(r, index)
        requires hasLeavesIndexedFrom(r2, index)

        requires leavesIn(r) == leavesIn(r2)

        ensures r.v == r2.v

        {
            if height(r) == 1 {
                //  Thanks Dafny
            } else {
                //  Induction on lc and rc and combine root with f
                match (r, r2) 
                    case (Node(_, lc, rc), Node(_, lc2, rc2)) => 
                        //  Check pre-conditions on lc rc before induction
                        childrenInCompTreesHaveHeightMinusOne(r);
                        childrenInCompTreesHaveHeightMinusOne(r2);
                        childrenCompTreeValidIndex(r, height(r), index);
                        childrenCompTreeValidIndex(r2, height(r2), index);
                        completeTreeNumberLemmas(r);
                        completeTreeNumberLemmas(r2);
                        childrenInCompTreesHaveHalfNumberOfLeaves(r, height(r));
                        childrenInCompTreesHaveHalfNumberOfLeaves(r2, height(r2));

                        calc == {
                            r.v;
                            f(lc.v, rc.v);
                            { sameLeavesSameRoot(lc, lc2, f, index); }
                            f(lc2.v, rc.v);
                            { sameLeavesSameRoot(rc, rc2, f, index + power2(height(r) - 1) / 2); }
                            f(lc2.v, rc2.v);
                            r2.v;
                        }
            }
        }

 }