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

include "../helpers/Helpers.dfy"
include "../trees/Trees.dfy"
include "../MerkleTrees.dfy"
include "../seqofbits/SeqOfBits.dfy"
include "../trees/CompleteTrees.dfy"
include "../paths/PathInCompleteTrees.dfy"
include "../helpers/SeqHelpers.dfy"

module DiffTreeProof { 

    import opened Helpers
    import opened Trees
    import opened MerkleTrees
    import opened SeqOfBits
    import opened CompleteTrees
    import opened PathInCompleteTrees
    import opened SeqHelpers

    import opened DiffTree

    lemma leftSiblingsInMerkle(
            r: Tree<int>, r': Tree<int>, 
            l : seq<int>, l' : seq<int>, 
            k: nat, 
            b : seq<int>, 
            // f : (T, T) -> T,
            p :seq<bit>, a : int 
            ,index: nat
            )
    
        //  Add this requirement first as otherwise the two requires
        //  isMerkle2 are very hard to prove and the solver may time out.
        requires 2 <= height(r) == height(r')

        // requires isCompleteTree(r)
        // requires isCompleteTree(r')

        /** Two merkle trees for two lists l and l'. */
        requires |l| == |l'| == |leavesIn(r)| == |leavesIn(r')| == power2(height(r) - 1)
        requires isMerkle2(r, l, diff)
        requires isMerkle2(r', l', diff)
        
        // requires hasLeavesIndexedFrom(r, index)
        // requires hasLeavesIndexedFrom(r', index)

        // requires 
        /** A leaf which is not the last one. */
        requires k < power2(height(r) - 1) - 1

        /** l has k values and beyond zero. */
        requires forall i :: k < i < |l| ==> l[i] == 0
        /** l' has k + 1 values and beyond zeros. First k is same as l. */
        requires forall i :: 0 <= i <= k ==> l'[i] == l[i] 
        requires forall i :: k + 1 < i < |l'| ==> l'[i] == 0 
        requires l'[k + 1] == a
        
        /** Path p to k-th leaf. */
        requires p == natToBitList2(k, height(r) - 1)
        //  Same as nodeAt(p, r) == leavesIn(r)[k]

        //  PC0
        // ensures 1 <= |p| == height(r) - 1 == height(r') - 1

        /** PostC 1: a path to the non-last leaf has a zero */
        ensures exists i :: 0 <= i < |p| && p[i] == 0
        
        /** PostC 2: r and r' agree on values of left siblings. */
        ensures 
             forall i :: 0 <= i < |p| && nextPath(p)[i] == 1 ==> 
                    siblingAt(take(nextPath(p), i + 1), r).v
                    ==
                    siblingAt(take(nextPath(p), i + 1), r').v
    {
        //  Proof of PC0

        //  Proof of PostC1
        assert(k < power2(height(r) - 1));
        assert(height(r) - 1 >= 1);
        bitToNatToBitsIsIdentity(k, height(r) - 1);
        // calc == {
            // bitListToNat(p);
            // {  assert(p == natToBitList2(k, height(r) - 1)); }
            // bitListToNat(natToBitList2(k, height(r) - 1));
            // { bitToNatToBitsIsIdentity(k, height(r) - 1); }
            // k;
            // < power2(height(r) - 1);
        // }
        // //  Apply lemma for bitListToNat(p) < power2(height(r) - 1)
        pathToNoLasthasZero(p);
        assume(exists i :: 0 <= i < |p| && p[i] == 0);
        
        //  Proof of PostC2
        if |p| == 1 {
            //  because of PostC1, p path to k-th leaf and not last one, p must be [0]
            assert(p == [0]);
            //  nextPath(p) == [1]
            calc == {
                nextPath(p) ;
                nextPath([0]);
                init([0]) + [1];
                [] + [1];
                calc == {
                    [] + [1];
                    [1];
                }
                [1];
            }
            forall (i : nat | 0 <= i < |p| && nextPath(p)[i] == 1) 
                    ensures siblingAt(take(nextPath(p), i + 1), r).v
                        ==
                        siblingAt(take(nextPath(p), i + 1), r').v
            {
                assert(i == 0);
                //  The trees r and r' both have 3 nodes r, lcr, rcc and r', lcr', rcr'
                //  The proof is easy for this simple case as leavesIn(r) and leavesIn(r')
                //  give the values of left siblings.
                calc == {
                    siblingAt(take(nextPath(p), 1), r).v;
                    siblingAt([1], r).v;
                    nodeAt([0], r).v;
                    leavesIn(r)[0].v;
                    leavesIn(r')[0].v;
                    siblingAt(take(nextPath(p), 1), r').v;
                }
            }
        } else {
            //  In this case |p| >= 2
            //  Height(r) > 2, induction on left and right children
            // assert(height(r) >= 2);
            // assert(k < |leavesIn(r)|);
            // assert(isCompleteTree(r));
            //  
            // calc == {
            //     bitListToNat(p);
            //     bitListToNat(natToBitList2(k, height(r) - 1));
            //     { bitToNatToBitsIsIdentity(k, height(r) - 1) ;}
            //     k;
            // }
            // indexOfLeafisIntValueOfPath2(p, r, k, index);
            // match (r, r') 
            //     case (Node(_, lc, rc), Node(_, lc', rc')) =>

                forall (i : nat | 0 <= i < |p| && nextPath(p)[i] == 1) 
                        ensures siblingAt(take(nextPath(p), i + 1), r).v
                            ==
                            siblingAt(take(nextPath(p), i + 1), r').v
                {
                    assume(
                            siblingAt(take(nextPath(p), i + 1), r).v
                            ==
                            siblingAt(take(nextPath(p), i + 1), r').v
                        );

                    // if (first(p) == 0) {
                    //     //  case path is to leaf in lc
                    //     // initPathDeterminesIndex(r, p, k, index);
                    //     // assert(k <  power2(height(r) - 1)/2);
                    //     assume(
                    //         siblingAt(take(nextPath(p), i + 1), r).v
                    //         ==
                    //         siblingAt(take(nextPath(p), i + 1), r').v
                    //     );

                    // } else {
                    //     //  first(p) == 1, rc
                    //     assume(
                    //         siblingAt(take(nextPath(p), i + 1), r).v
                    //         ==
                    //         siblingAt(take(nextPath(p), i + 1), r').v
                    //     );
                    // }
                    
                }
        }
       
    }

}
