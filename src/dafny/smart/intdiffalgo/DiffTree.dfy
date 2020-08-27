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

include "../helpers/Helpers.dfy"
include "../trees/Trees.dfy"
include "../MerkleTrees.dfy"
include "../seqofbits/SeqOfBits.dfy"
include "../trees/CompleteTrees.dfy"
include "../paths/PathInCompleteTrees.dfy"
include "../helpers/SeqHelpers.dfy"

module DiffTree { 

    import opened Helpers
    import opened Trees
    import opened MerkleTrees
    import opened SeqOfBits
    import opened CompleteTrees
    import opened PathInCompleteTrees
    import opened SeqHelpers

    //  Trees holding integer values as attribute.
    type Intnode = Tree<int>

    /** 
     *  Difference between two integers.
     *
     *  @note:  This could be inlined in the predicate
     *          isDecoratedWithDiff, but we may use another 
     *          function later, so we factor it out.
     */
    function method diff(a: int, b : int) : int 
    {
        a - b
    }
    
    /**
     *  Check that a decorated tree correctly stores the diff attribute. 
     */
    predicate isDecoratedWithDiff(r: Tree<int>) 
    {
        isDecoratedWith(diff, r)
    } 

    /** 
     *  Defines the Int Tree associated with a given sequence.
     *  
     *  @note   T   his function does not compute the tree but rather
     *              defines its properties: correctly stores the attribute
     *              `diff` and the leftmost |l| leaves store l.
     *
     *  @param  l   
     */
    function buildMerkleDiff(l: seq<int>, h : nat) : Tree<int> 
        requires h >= 1
        /** Tree has enough leaves to store `l`. */
        requires |l| <= power2(h - 1)      
    {
        buildMerkle(l , h, diff, 0)
    }

    /**
     *  The tree decorated with zeroes.
     *  
     *  @param  r   A tree.
     *  @returns    True if and only if all values are zero.
     */
    predicate isZeroTree(r : Tree<int>) 
    {
        isConstant(r, 0)
    }

    /**
     *  If all leaves are zero and tree is decorated with diff, then
     *  all nodes are zero, and tree is ZeroTree.
     */
    lemma {:induction r} allLeavesZeroImplyAllNodesZero(r: Tree<int>) 
        requires isDecoratedWithDiff(r)
        requires forall l :: l in leavesIn(r) ==> l.v == 0
        ensures forall l :: l in nodesIn(r) ==> l.v == 0 
        ensures isZeroTree(r)
    {   //  Thanks Dafny
    }

    /**
     *  For a tree of height >= 2, decorated with diff,
     *  If for some k <= power2(height(r) - 1) / 2, all leaves are zero,
     *  then the right child is the zero tree.
     */
    lemma {:induction r} rightHalfOfListZeroImpliesRightTreeZero(r: Tree<int>, k : nat) 
        requires isCompleteTree(r)
        /** `r` is decorated with attribute `f`. */
        requires isDecoratedWith(diff, r)
        requires height(r) >= 2

        /**  all leaves at index >= k are zero. */
        requires k <= power2(height(r) - 1) / 2
        requires forall i :: k <= i < |leavesIn(r)| ==> leavesIn(r)[i].v == 0

        ensures match r 
            case Node(_, lc, rc) => isZeroTree(rc) && rc.v == 0
    {   
        match r 
            case Node(_, lc, rc) =>
                //  First show that all leaves in rc are zero
                forall (i : int |  0 <= i < |leavesIn(rc)|)
                    ensures leavesIn(rc)[i].v == 0
                    {
                        //  This is because there leaves of index >= k for which l[k] == leavesIn(r)[k] == 0
                        childrenInCompTreesHaveSameNumberOfLeaves(r);
                        assert(leavesIn(r)[i + power2(height(r) - 1)/2] == leavesIn(rc)[i ]);
                        assert(i + power2(height(r) - 1)/2 < |leavesIn(r)|);
                        calc >= {
                            i + power2(height(r) - 1)/2;
                            k;
                        }
                        calc == {
                            leavesIn(rc)[i].v;
                            { childrenInCompTreesHaveHalfNumberOfLeaves(r, height(r));}
                            leavesIn(r)[i + power2(height(r) - 1)/2].v;
                            0;
                        }
                    }
                //  Assert ore-condition of allLeavesZeroImplyAllNodesZero
                calc ==> {
                    forall i ::  0 <= i < |leavesIn(rc)| ==> leavesIn(rc)[i].v  == 0;
                    forall l :: l in leavesIn(rc) ==> l.v == 0;
                    { allLeavesZeroImplyAllNodesZero(rc); }
                    forall n :: n in nodesIn(rc) ==> n.v == 0 && isZeroTree(rc);
                    calc == {
                        rc;
                        nodesIn(rc)[0];
                    }
                    rc.v == 0 && isZeroTree(rc);
                }
    }

    /**
     *  For a complete tree, decorated with diff,
     *  If all the leaves on right side of the node after the path
     *  are zero, then all the right siblings on the path have value 0.
     *
     *  @note       The proof has several cases but is not hard.
     */
    lemma {:induction r} leavesRightOfNodeAtPathZeroImpliesRightSiblingsOnPathZero(r: Tree<int>, k : nat, p: seq<bit>, j : nat) 

        requires isCompleteTree(r)
        /** `r` is decorated with attribute `f`. */
        requires isDecoratedWith(diff, r)
        requires height(r) >= 2

        /**  all leaves after the k leaf are zero. */
        requires k < |leavesIn(r)|
        requires forall i :: k < i < |leavesIn(r)| ==> leavesIn(r)[i].v == 0

         /** Proper indexing. */
        requires hasLeavesIndexedFrom(r, j)
        /** p is the path to k-th leaf in r. */
        requires |p| == height(r) - 1
        requires nodeAt(p, r) == leavesIn(r)[k]

        /** For all right siblings on p, value of diff is zero. */
        ensures forall i :: 0 <= i < |p| ==> 
            p[i] == 0 ==> siblingAt(p[..i + 1], r).v == 0

        decreases r

    {   
        //  The tree is properly indexed and lc and rc properly indexed.
        childrenCompTreeValidIndex(r, height(r), j);

        forall ( i : nat | 0 <= i < |p|)
            ensures p[i] == 0 ==> siblingAt(p[..i + 1], r).v == 0
        {
            if (height(r) == 2) {
                //  Thanks Dafny
                if ( p[0] == 0 ) {
                    calc == {
                        siblingAt(p[..1], r).v ;
                        nodeAt([1], r).v;
                        { initPathDeterminesIndex(r, p, k, j); }
                        //  implies k == 0 and hence nodeAt([1], r).v == 0
                        0;
                    }
                }
            } else {
                //  height(r) >= 3, so lc and rc have children
                match r
                    case Node(v, lc, rc) => 
                        if (p[0] == 0) {
                            //  number of nodes and leaves in complete trees.
                            completeTreeNumberLemmas(r);
                            assert( k < power2(height(r) - 1));

                            //  First bit of a path determines range for index of target leaf.
                            initPathDeterminesIndex(r, p, k, j);
                            assert(p[0] == 0 ==> k < power2(height(r) - 1) / 2);

                            //  Conclusion if i == 0 sibling is rc, and otherwise
                            //  siblings are in lc
                            if ( i == 0 ) {
                                //  p[0] == 0 and i == 0
                                calc == {
                                    siblingAt(p[..0 + 1], r).v;
                                    siblingAt([p[0]], r).v;
                                    nodeAt([p[0]][..|[p[0]]| - 1] + [1] , r).v;
                                    nodeAt([1],r).v;
                                    rc.v ;
                                    {  rightHalfOfListZeroImpliesRightTreeZero(r, k + 1); }
                                    0;
                                }
                            }
                            else {
                                //   i >= 1, siblings are in lc
                                //  Check pre-condition before applying induction on lc
                                childrenInCompTreesHaveSameNumberOfLeaves(r);
                                assert(|leavesIn(r)[.. power2(height(r) - 1)/2]| == |leavesIn(lc)|);
                                //  Induction on lc
                                leavesRightOfNodeAtPathZeroImpliesRightSiblingsOnPathZero(
                                    lc, 
                                    k, 
                                    p[1..], 
                                    j);

                                //  We conclude that:
                                assert(forall j :: 0 <= j < |p[1..]| ==> p[1..][j] == 0 ==> siblingAt(p[1..][..j + 1], lc).v == 0);

                                //  We can use the fact that siblingAt(siblingAt(p[..i + 1], r) is
                                //  siblingAt(p[1..][.. i], lc) and p[1..][i] == p[..i + 1]
                                simplifySiblingAtFirstBit(p[..i + 1], r);
                                calc == {
                                    siblingAt(p[..i + 1], r);
                                    siblingAt(p[..i + 1][1..], lc);
                                    calc == {
                                        p[1..][..i];
                                        p[1.. i + 1];
                                    }
                                    siblingAt(p[1..][.. i], lc);
                                }
                            } 
                        } else {
                            //  p[0] == 1 
                            //  Split in case i == 0 and i >= 1
                            if ( i == 0 ) {
                                //  nothing to prove as p[0] == 1
                            } else {
                                //  i >= 1
                                //  siblingAt(p[..i + 1], r) are  in rc and all leaves in rc are zero
                                completeTreeNumberLemmas(r);
                                initPathDeterminesIndex(r, p, k, j);
                                assert( k >= power2(height(r) - 1) / 2);

                                childrenInCompTreesHaveSameNumberOfLeaves(r);
                                assert(|leavesIn(r)[power2(height(r) - 1)/2..]| == |leavesIn(rc)|);

                                //  Induction on rc
                                leavesRightOfNodeAtPathZeroImpliesRightSiblingsOnPathZero(
                                    rc, 
                                    k - power2(height(r) - 1)/2,
                                     p[1..],
                                    j + power2(height(r) - 1)/2);
                                //  We conclude that 
                                assert(forall i :: 0 <= i < |p[1..]| ==> 
                                    p[1..][i] == 0 ==> siblingAt(p[1..][..i + 1], rc).v == 0);

                                //  We now prove that siblingAt(siblingAt(p[..i + 1], r) is
                                //  siblingAt(p[1..][.. i], rc) and p[1..][i] == p[..i + 1]
                                simplifySiblingAtFirstBit(p[..i + 1], r);
                                calc == {
                                    siblingAt(p[..i + 1], r);
                                    siblingAt(p[..i + 1][1..], rc);
                                    calc == {
                                        p[1..][..i];
                                        p[1.. i + 1];
                                    }
                                    siblingAt(p[1..][.. i], rc);
                                }
                                //  hence p[].. i + 1] == 0 ==> siblingAt(p[..i + 1], r).v == 0
                            }
                        }   
            }
        }
    }

   
}
