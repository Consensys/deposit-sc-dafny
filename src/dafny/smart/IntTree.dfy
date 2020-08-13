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
include "MerkleTrees.dfy"
include "SeqOfBits.dfy"
include "CompleteTrees.dfy"
include "PathInCompleteTrees.dfy"
include "SeqHelpers.dfy"

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
     *  Equivalent characterisation of zero trees.
     */
    lemma {:induction r} isZeroTreeiffAllNodesZero(r : Tree<int>) 
            ensures (forall l :: l in nodesIn(r) ==> l.v == 0) <==> isZeroTree(r)
    {   //  Thanks Dafny
    } 

    /**
     *  If all leaves are zero and tree is decorated with diff, then
     *  all nodes are zero.
     */
    lemma {:induction r} allLeavesZeroImplyAllNodesZero(r: Tree<int>) 
        requires isDecoratedWithDiff(r)
        requires forall l :: l in leavesIn(r) ==> l.v == 0
        ensures forall l :: l in nodesIn(r) ==> l.v == 0 
    {   //  Thanks Dafny
    }

    lemma {:induction r} p3(r: Tree<int>, l : seq<int>, k : nat) 
        requires height(r) >= 2
        requires |l| == |leavesIn(r)|
        requires isMerkle2(r, l, diff)
        /**  all leaves in rc are 0 (plus maybe some in lc). */
        requires k <= power2(height(r) - 1) / 2
        requires forall i :: k <= i < |l| ==> l[i] == 0

        ensures match r 
            case Node(_, lc, rc) =>
                forall i :: 0 <= i < |leavesIn(rc)| ==> leavesIn(rc)[i].v == 0
    {   
        match r 
            case Node(_, lc, rc) =>
                forall (i : int |  0 <= i < |leavesIn(rc)|)
                    ensures leavesIn(rc)[i].v == 0
                    {
                        childrenInCompTreesHaveSameNumberOfLeaves(r);
                        assert(leavesIn(r)[i + power2(height(r) - 1)/2] == leavesIn(rc)[i ]);
                        assert(i + power2(height(r) - 1)/2 < |leavesIn(r)|);
                    }
    }

    /**
     *  If all leaves in rc are 0, then rc.v itself is zero.
     */
    lemma {:induction r} p4(r: Tree<int>, l : seq<int>, k : nat) 
        requires height(r) >= 2
        requires |l| == |leavesIn(r)|
        requires isMerkle2(r, l, diff)
        /**  all leaves in rc are 0 (plus maybe some in lc). */
        requires k <= power2(height(r) - 1) / 2
        requires forall i :: k <= i < |l| ==> l[i] == 0
        
        ensures match r 
            case Node(_, lc, rc) => rc.v == 0
    {   
        match r 
            case Node(_, lc, rc)=>
                p3(r, l, k);
                allLeavesZeroImplyAllNodesZero(rc);
    }

    lemma {:induction r} t2(r: Tree<int>, l : seq<int>, k : nat, p: seq<bit>, j : nat) 

        /** Merkle tree. */
        requires height(r) >= 2
        requires |l| == |leavesIn(r)|
        requires isMerkle2(r, l, diff)
        requires hasLeavesIndexedFrom(r, j)

        /** Proper indexing. */

        /**  all leaves after the k leaf are zero. */
        requires k < |leavesIn(r)|
        requires forall i :: k < i < |l| ==> l[i] == 0

        /** p is the path to k leaf in r. */
        requires |p| == height(r) - 1
        requires nodeAt(p, r) == leavesIn(r)[k]

        /** For all right siblings on p, value of diff is zero. */
        ensures forall i :: 0 <= i < |p| ==> 
            p[i] == 0 ==> siblingAt(p[..i + 1], r).v == 0

        decreases r

    {   
        childrenCompTreeValidIndex(r, height(r), j);

        forall ( i : nat | 0 <= i < |p|)
            ensures p[i] == 0 ==> siblingAt(p[..i + 1], r).v == 0
        {
            if (height(r) == 2) {
                //  Thanks Dafny
                assert(|p| == 1);
                // assume(isValidIndex(r,j));
                // assert(isCompleteTree(r));
                childrenCompTreeValidIndex(r, height(r), j);
                if (p[0] == 0) {
                    match r 
                        case Node(_, lc, rc) => 
                            assert(siblingAt(p[..1], r) ==  rc);
                            assert(siblingAt(p[..1], r) ==  leavesIn(r)[1]);
                            assert(|leavesIn(r)| == 2);
                            nodeLoc2(r, p, k, j);
                            assert(k < 1);
                } else {
                    //  p[0] == 1 
                    assert(p[0] == 0 ==> siblingAt(p[..1], r).v == 0);
                }
            } else {
                //  height(r) >= 3, so lc and rc have children
                match r
                    case Node(v, lc, rc) => 
                        childrenCompTreeValidIndex(r, height(r), j);
                        if (p[0] == 0) {
                            completeTreeNumberLemmas(r);
                            assert( k < power2(height(r) - 1));
                            nodeLoc2(r, p, k, j);
                            assert(p[0] == 0 ==> k < power2(height(r) - 1) / 2);
                            //  siblings in lc
                            if ( i >= 1 ) {
                            
                                assert(height(lc) >= 2);
                                assert(0 <= |p[..i][1..]| );
                                assert (0 <= |p[..i][1..]| < height(lc));
                                assert(isCompleteTree(lc));
                                assert( p == [0] + p[1..]);

                                simplifySiblingAtFirstBit(p[..i + 1], r);
                                // assert(siblingAt(p[..i + 1], r) == nodeAt(p[..i + 1], r));
                                // assert(nodeAt(p[..i + 1], r) == nodeAt(p[..i + 1][1..], lc));
                                assert(siblingAt(p[..i + 1], r) == siblingAt(p[..i + 1][1..], lc));


                                assert(isCompleteTree(r));
                                completeTreeNumberLemmas(r);
                                assert(|l| == power2(height(r) - 1));
                                childrenInCompTreesHaveSameNumberOfLeaves(r);
                                assert(|l[.. power2(height(r) - 1)/2]| == |leavesIn(lc)|);
                                assert(|l[.. power2(height(r) - 1)/2]| == power2(height(r) - 1)/2);
                                assert( k <= |leavesIn(lc)|); 
                                t2(lc, l[.. power2(height(r) - 1)/2], k, p[1..], j);

                                assert(forall j :: 0 <= j < |p[1..]| ==> p[1..][j] == 0 ==> siblingAt(p[1..][..j + 1], lc).v == 0);

                                // prefixOfSuffix(p, i);   
                                assert(p[1..][..i] == p[1.. i + 1]); 
                                assert(siblingAt(p[..i + 1], r) == siblingAt(p[1..][.. i], lc));
                                assert(p[1..][i - 1] == 0 ==> siblingAt(p[1..][.. i], lc).v == 0);
                                assert(p[i] == 0 ==> siblingAt(p[1..][.. i], lc).v == 0);

                                // prefixOfSuffix(p, i);    
                                assert(p[i] == 0 ==> siblingAt(p[1..i + 1], lc).v == 0);
                                assert(p[i] == 0 ==> siblingAt(p[..i + 1], r).v == 0);

                            } else {
                                //  p[0] == 0 and i == 0
                                assert(siblingAt(p[..i + 1], r) == siblingAt(p[..0 + 1], r));
                                calc == {
                                    siblingAt(p[..0 + 1], r);
                                    siblingAt([p[0]], r);
                                    nodeAt([p[0]][..|[p[0]]| - 1] + [1] , r);
                                    nodeAt([1],r);
                                }
                                //  case of first sibling which is rc.
                                //  All leaves in rc are zero
                                // p1(r, k);
                                assert(k + 1 <= power2(height(r) -1 )/ 2);
                                // foo111(p[..i + 1], r);
                                // p3(r, l, k + 1);
                                p4(r, l, k + 1);
                                //  assume(
                                //         forall i :: 0 <= i < |p| ==> 
                                //         p[i] == 0 ==> siblingAt(p[..i + 1], r).v == 0
                                //     );
                            }

                        } else {
                            //  p[0] == 1 
                            //  nothing to prove for siblingAt(p[..1], r).v == 0
                            if ( i == 0) {
                                assert(p[0] == 0 ==> siblingAt(p[..1], r).v == 0);
                            } else {
                                completeTreeNumberLemmas(r);
                                nodeLoc2(r, p, k, j);
                                assert( k >= power2(height(r) - 1) / 2);
                                childrenInCompTreesHaveSameNumberOfLeaves(r);
                                assert(|l[power2(height(r) - 1)/2..]| == |leavesIn(rc)|);
                                t2(rc, l[power2(height(r) - 1)/2..], k - power2(height(r) - 1)/2, p[1..],
                                 j + power2(height(r) - 1)/2);
                                assert(p[0] == 0 ==> k < power2(height(r) - 1) / 2);
                                // prefixOfSuffix(p, i);   
                                assert(p[1..][..i] == p[1.. i + 1]); 

                                simplifySiblingAtFirstBit(p[..i + 1], r);

                                // assert(siblingAt(p[..i + 1], r) == nodeAt(p[..i + 1], r));
                                // assert(nodeAt(p[..i + 1], r) == nodeAt(p[..i + 1][1..], rc));
                                assert(siblingAt(p[..i + 1], r) == siblingAt(p[..i + 1][1..], rc));

                                assert(siblingAt(p[..i + 1], r) == siblingAt(p[1..][.. i], rc));
                                assert(p[1..][i - 1] == 0 ==> siblingAt(p[1..][.. i], rc).v == 0);
                                assert(p[i] == 0 ==> siblingAt(p[1..][.. i], rc).v == 0);
                                assert(p[i] == 0 ==> siblingAt(p[1..i + 1], rc).v == 0);
                                assert(p[i] == 0 ==> siblingAt(p[..i + 1], r).v == 0);

                            }
                        }   
            }
        }
    }


    /**
     *  Incremental algorithm.
     *
     *  @todo   Add data structures and complete method add to
     *          correctly compute diffRoot. 
     */
    class IntTree {

        /**  The root tracking the Merkle Tree. */
        ghost var root : Tree<int>

        /** Height of the tree */
        var h : nat 

        /** diffRoot, the value of diff on the root. */
        var diffRoot : int

        /** Number of elements in the tree. */
        // var counter : nat

        /** The list of ints stored in the tree.  */
        ghost var store : seq<int>

        /** A valid tree. */
        predicate isValid() 
            requires isCompleteTree(root)
            reads this
        {
            //  Use lemmas relating number of leaves and height of a complete tree.
            completeTreeNumberLemmas(root);

            //  The tree is correctly decorated by diff.
            isDecoratedWithDiff(root)
            //  diffRoot is the value of diff on root.
            && diffRoot == root.v
            //  height preserved.
            && h == height(root) 
            && 0 <= |store| <= power2(h - 1)
            && |leavesIn(root)| == power2(h - 1)

            //  tree leftmost leaves are in store.
            && treeLeftmostLeavesMatchList(store, root, 0)
        }

        /**
         *  Initial tree of height initH and all leaves set to 0.
         */
        constructor(initH: nat) 
            requires initH >= 1
            ensures height(root) == h == initH
            ensures treeLeftmostLeavesMatchList([], root, 0)
            ensures store == []
            ensures isCompleteTree(root)
            ensures isValid()

        
        
        /**
         *  The Merkle tree of height `h` for the empty list is the 
         *  zero (complete) tree of height `h`.
         */
        // lemma merkleEmptyListIsZeroTree(h : nat)
        //     requires h >= 1 
        //     ensures isZeroTree(buildMerkle([], h))
        // {
        //     allLeavesZeroImplyAllNodesZero(buildMerkle([], h));
        //     isZeroTreeiffAllNodesZero(buildMerkle([], h));
        // }   
       
       
        /**
         *  The leaf at index k < 2^(h - 1)/2 is in lc, and index >= 2^(h - 1)/2
         *  is in rc.
         *  @todo   Check whether this lemma is useful and not superseded by p3.
         */
        // lemma {:induction r} p1(r : Tree<int>, k : nat)
        //     requires isCompleteTree(r)
        //     requires height(r) >= 2
        //     requires 0 <= k < power2(height(r) - 1 ) 
        //     ensures match r 
        //         case Node(_, lc, rc )=> 
        //             ((0 <= k < power2(height(r) - 1 ) / 2) ==>
        //                 k < |leavesIn(lc)|
        //                 && leavesIn(r)[k] == leavesIn(lc)[k]
        //             )
        //             && 
        //                 (power2(height(r) - 1) / 2 <= k < power2(height(r) - 1) ==> 
        //                 && 0 <= k - power2(height(r) - 1)/2 < |leavesIn(rc)|
        //                 && k < |leavesIn(r)|
        //                 && leavesIn(r)[k] == leavesIn(rc)[k - power2(height(r) - 1)/2]
        //                 )
        // {
        //     completeTreesLeftRightHaveSameNumberOfLeaves(r);
        //     completeTreesLeftRightChildrenLeaves(r, height(r)) ;
        // }


        
       

        /**
         *  Values of the nodes on the right of a path to e in Merkle(l :+ e,h)
         *  are all zeroes.
         */
        // lemma nodesOnRightSiblingsZero(p: seq<bit>, r: Tree<int>, l: seq<int>, e : int, h: nat)
        //     requires h == height(r) >= 1
        //     /** */
        //     requires |l| + 1 <= |leavesIn(r)|
        //     requires isMerkle(r, l + [e], diff, 0)
        //     /** `p` is a path to `e`. */
        //     requires |p| == h - 1
        //     requires nodeAt(p, r).id == p 

        //     requires |l| + 1 <=  |leavesIn(r)| / 2
        //     ensures forall n :: 0 <= n < |p| ==> 
        //         p[n] == 0 ==> siblingAt(p, r).v == 0 
        // {
        //     if h == 1 {
        //         //  Thanks Dafny
        //     }
        //     else {
        //         // match r 
        //         //     case Node(_, lc, rc) =>
        //     }
        // }

        /**
         *  The value of diff at the root of a well decorated tree is the value of
         *  the tree.
         */
        function hash_tree_root(r: Tree<int>) : int 
            requires isCompleteTree(r)
            requires isDecoratedWithDiff(r) 
        {
            r.v
        }

        /** 
         *  Add element e to the tree.
         *
         *  @param  e   The element to add to the store.
         *
         *  @todo       This algorithm should maintain the invariant
         *              `diffRoot == root.v`.
         */
        method add(e: int)

            requires isCompleteTree(root)
            requires h == height(root) 
            requires |store| < power2(h - 1)

            requires |leavesIn(root)| == power2(h - 1)
            requires isDecoratedWith(diff, root)
            requires treeLeftmostLeavesMatchList(store, root, 0)
            requires isMerkle(root, store, diff, 0)
            requires isValid()

            //  Store is updated
            ensures store == old(store) + [ e ]

            //  Preserves tree height and completeness
            ensures  old(h) == h
            //  Store is not full
            ensures isCompleteTree(root)

            ensures |leavesIn(root)| == power2(h - 1)

            //  diffRoot stores value of diff for store
            ensures isDecoratedWithDiff(root)
            ensures |store| <= power2(h - 1)
            ensures treeLeftmostLeavesMatchList(store, root, 0)

            //  The next one is not verified in the current version of this algo.
            // ensures diffRoot == root.v

            // ensures isValid()

            modifies this
        {
            //  Update store
            store := store + [ e ] ;
            
            //  Define new tree for updated store
            root := buildMerkleDiff(store, h);

            //  Compute the new diffRoot
            diffRoot := 0 ;
        }

    } 
}
