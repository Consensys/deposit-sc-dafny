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
include "PathInCompleteTrees.dfy"
include "../synthattribute/ComputeRootPath.dfy"
include "../seqofbits/SeqOfBits.dfy"
include "../helpers/SeqHelpers.dfy"
include "../trees/Trees.dfy"

/**
 *  Provide computation of values of left siblings on next path.
 *
 *  1. `computeLeftSiblingOnNextPath` computes the left siblings on the next path using
 *      the values on the path and on the left of the path.
 *  2.  `computeLeftSiblingOnNextPathFromLeftRight` computes the left siblings on the next path using
 *      the values on the left and right of path only.
 *  3.  `computeLeftSiblingOnNextPathIsCorrect` proves that `computeLeftSiblingOnNextPath` is correct for a tree.
 *  4.  As `computeLeftSiblingOnNextPathFromLeftRight` computes the same result as `computeLeftSiblingOnNextPath`
 *      it follows that it is correct for a tree too. The proof of 4. uses intermnediate `bridge` algorithms
 *      `computeLeftSiblingOnNextPathBridge` and `computeLeftSiblingOnNextPathBridgeV2`.
 *  
 *  The correctness proof of `computeLeftSiblingOnNextPathFromLeftRight` 
 */
module NextPathInCompleteTreesLemmas {

    import opened CompleteTrees
    import opened Helpers
    import opened PathInCompleteTrees
    import opened ComputeRootPath
    import opened SeqOfBits
    import opened SeqHelpers
    import opened Trees 

    ///////////////////////////////////////////////////////////////////////////
    //  Main algorithms
    ///////////////////////////////////////////////////////////////////////////

    /**
     *  Compute the left siblings of nextPath.
     *
     *  @param  p       A path.
     *  @param  v1      The values of the nodes on the path.
     *  @param  left    The values of the nodes that are left siblings of nodes on the path.
     *  @returns        The values of the nodes that are left siblings of nextPath(p).
     */
    function method computeLeftSiblingOnNextPath<T>(p: seq<bit>, v1 : seq<T>, left : seq<T>) : seq<T>
        requires 1 <= |p| 
        requires |v1| == |left| == |p|
        ensures |computeLeftSiblingOnNextPath(p, v1, left)| == |v1|

        decreases p
    {
        if |p| == 1 then
            /*  If p[0] == 0, we use the value on the path i.e v1, and otherwise p[0] == 1 we can choose
             *  whatever we want as at this level as the sibling on the next path is on is right siblings
             *  We choose to use left i.e. keep the same value for sibling at this level,  in order to
             *  enable optimisations in the imperative version of the algorithm where a single array is used.
             */
            if first(p) == 0 then v1 else left 
        else 
            assert(|p| >= 2);
            if last(p) == 0 then 
                /*  This is where the next path flips side. The next path is of the form init(p) + [1].
                 *  The prefix of p and of nextPath(p) share the same siblings, and the the left sibling 
                 *  on nextPath at this level is the elft child, so we use its value [last(v1)].
                 */
                init(left) + [last(v1)]
            else 
                assert(last(p) == 1);
                /*  The nextPath is of the form nextPath(init(p)) + [0].
                 *  So the sibling at this level is a right sibling and the value we store in the
                 *  result for this result is irrelevant. We choose to keep the value of the previous left
                 *  sibling from left in order to allow optimisations in the impertive version of the algorithm.
                 */
                computeLeftSiblingOnNextPath(init(p), init(v1), init(left)) + [last(left)]
    } 

    /**
     *  Compute the left siblings of nextPath using letf and right siblings of current path and seed.
     *
     *  @param  p   A path.
     *  @param  left        The values of the left siblings of nodes on path `p`.
     *  @param  right       The values of the right siblings of nodes on path `p`.
     *  @param  f           The binary operation to compute.
     *  @param  seed        The value at the end of the path.
     *  @returns            The values of the nodes that are left siblings of nextPath(p).
     */
    function method computeLeftSiblingOnNextPathFromLeftRight<T>(p: seq<bit>, left : seq<T>, right : seq<T>, f : (T, T) -> T, seed : T) : seq<T>
        requires 1 <= |p| 
        requires |left| == |right| == |p|

        ensures computeLeftSiblingOnNextPathFromLeftRight(p, left, right, f, seed)
            == computeLeftSiblingOnNextPath(p, computeAllUp(p, left, right, f, seed), left)

        decreases p
    {
        if |p| == 1 then
            if first(p) == 0 then [seed] else left 
        else 
            assert(|p| >= 2);
            if last(p) == 0 then 
                init(left) + [seed]
            else 
                assert(last(p) == 1);
                computeLeftSiblingOnNextPathFromLeftRight(init(p), init(left), init(right), f, f(last(left), seed)) + [last(left)]
    } 

    ///////////////////////////////////////////////////////////////////////////
    //  Main correctness proof.
    ///////////////////////////////////////////////////////////////////////////


    /**
     *  computeLeftSiblingOnNextPathFromLeftRight is correct in a tree.
     *
     *  @param  p       A path.
     *  @param  r       A tree.
     *  @param  left    The value of `f` on siblings on path `p`.
     *  @param  right   The value of `f` on siblings on path `p`.
     *  @param  f       A binary operation.
     *  @param  seed    A value.
     */
    lemma {:induction p, r, left, right} computeLeftSiblingOnNextPathFromLeftRightIsCorrectInATree<T>(
            p: seq<bit>, r : Tree<T>, left : seq<T>, right : seq<T>, f : (T, T) -> T, seed : T, k : nat)
    
        requires isCompleteTree(r)
        requires isDecoratedWith(f, r)
        requires hasLeavesIndexedFrom(r, 0)
        requires k < |leavesIn(r)| - 1
        requires 1 <= |p| == height(r) 
        requires nodeAt(p, r) == leavesIn(r)[k]
        requires seed == nodeAt(p,r).v 

        requires |p| == |left| == |right|

        /** Left and right contains siblings left and right values.  */
        requires forall i :: 0 <= i < |p| ==>
            siblingAt(take(p, i + 1), r).v == 
                if p[i] == 0 then 
                    right[i]
                else 
                    left[i]

        ensures  exists i :: 0 <= i < |p| && p[i] == 0
        /** The values computed by computeLeftSiblingOnNextPath coincide with leftsiblings on `p`. */
        ensures forall i :: 0 <= i < |p| && nextPath(p)[i] == 1 ==> 
                computeLeftSiblingOnNextPathFromLeftRight(p, left, right, f, seed)[i] == siblingAt(take(nextPath(p), i + 1),r).v

    {
        //  Prove that p has a zero
        pathToLeafInInitHasZero(p, r, k);
        //  Prove that computeAllUp(p, left, right, f, seed) is same as values on each node on the path
        computeAllIsCorrectInATree(p, r, left, right, f, k, seed, 0);
       
        //  Use the proof that computeAllUp == tail(computeAllUp2)
        computeAllUpEqualsComputeAll(p, left, right, f, seed);
        shiftComputeAll(p, left, right, f, seed);
        assert(computeAllUp(p, left, right, f, seed) == tail(computeAllUp2(p, left, right, f, seed)));
        computeLeftSiblingOnNextPathIsCorrect(p, r, computeAllUp(p, left, right, f, seed), left);
    }

    ///////////////////////////////////////////////////////////////////////////
    //  Helper functions and lemmas.
    ///////////////////////////////////////////////////////////////////////////
    /**
     *  Next path from a leaf must go to the next leaf
     *  
     *  @param  p   A path to the k-th leaf of `r`
     *  @param  r   A complete tree.
     *  @param  k   The index of a leaf in r that is not the last leaf.
     */
    lemma {:induction p, r} nextPathNextLeaf(p: seq<bit>, r :  Tree, k : nat) 
        requires isCompleteTree(r)                              
        requires hasLeavesIndexedFrom(r, 0)
        requires 1 <= |p| == height(r)                    
        requires 0 <= k < |leavesIn(r)| - 1                     
        requires bitListToNat(p) == k               

        ensures exists i ::  0 <= i < |p| && p[i] == 0         //  P1
        ensures nodeAt(nextPath(p), r) == leavesIn(r)[k + 1]   //  P2
        ensures bitListToNat(nextPath(p)) == k + 1             //  P3
    {
        //  Proof of P1
        calc ==> {
            true;
            { pathToLeafInInitHasZero(p, r, k); }
            exists i ::  0 <= i < |p| && p[i] == 0;
        }

        //  Proof of P3 and P2
        //  We just need to prove that bitListToNat(nextpath(p)) == k + 1 
        calc == {
            bitListToNat(nextPath(p));
            //  bitListToNat(nextPath(p)) == bitListToNat(p) + 1
            { nextPathIsSucc(p); }
            bitListToNat(p) + 1;
            { indexOfLeafisIntValueOfPath(p, r, k); }
            // ==> bitListToNat(p) == k
            k + 1;
        }
        //  and apply indexOfLeafisIntValueOfPath
        indexOfLeafisIntValueOfPath(nextPath(p), r, k + 1);
    }

    /**
     *  computeLeftSiblingOnNextPath returns values on left siblings of next path.
     *
     *  @param  p   A path with at least one zero (i.e. not to the last leaf so that there is a path to next leaf.)
     *  @param  r   A complete tree.
     *  @param  v1  The values on the nodes of the path (except root of r).
     *  @param  v2  The values on the left siblings of the nodes of the path.
     */
    lemma {:induction p, v1, v2} computeLeftSiblingOnNextPathIsCorrect<T>(p: seq<bit>, r :  Tree<T>, v1 : seq<T>, v2 : seq<T>)
        requires isCompleteTree(r)                              
        requires 1 <= |p| <= height(r)     
        requires exists i :: 0 <= i < |p| && p[i] == 0  //  Req1
        requires |v1| == |v2| == |p|
        requires forall i :: 0 <= i < |p| ==>           //  Req2
            v1[i] == nodeAt(take(p, i + 1),r).v 
        requires forall i :: 0 <= i < |p| ==>           //  Req3 
            p[i] == 1 ==> v2[i] == siblingAt(take(p, i + 1),r).v 

        /** The values computed by computeLeftSiblingOnNextPath coincide with leftsiblings on `p`. */
        ensures forall i :: 0 <= i < |p| && nextPath(p)[i] == 1 ==> 
                computeLeftSiblingOnNextPath(p, v1, v2)[i] == siblingAt(take(nextPath(p), i + 1),r).v

        decreases p 
    {    
        forall (i : int |  0 <= i < |p| && nextPath(p)[i] == 1)
            ensures computeLeftSiblingOnNextPath(p, v1, v2)[i] == 
                                    siblingAt(take(nextPath(p), i + 1),r).v
        {
            if |p| == 1 {
                //  i must be zero and because of Req1, p[0] == 0
                assert(i == 0 && p[0] == 0);
                assert(p == [0]);
                //  Next path is [1]
                assert(nextPath(p) == [1]);
                calc == {
                    computeLeftSiblingOnNextPath(p, v1, v2)[i];
                    //  Definition of computeLeftSiblingOnNextPath
                    v1[0];
                    nodeAt(take(p, 1),r).v;
                    nodeAt([0],r).v;
                    nodeAt(take([1],0) + [0],r).v;
                    siblingAt([1],r).v;
                    siblingAt(take(nextPath(p), 1),r).v;
                }
            } else {
                //  |p| >= 2
                if (last(p) == 0) {
                    //  Next path must end with 1 and hence p[|p| - 1] == 0
                    calc == {
                        nextPath(p);
                        init(p) + [1];
                    }
                    if ( i < |p| - 1 ) {
                        //  Up to i, nextPath is same as p
                        calc == {
                            siblingAt(take(nextPath(p), i + 1), r).v ;
                            siblingAt(take(init(p) + [1], i + 1), r).v ;
                            //  take(init(p) + [1], i + 1) == take(init(p), i + 1) by
                            { seqAppendIndexLemmas(init(p), [1], i + 1) ; }
                            siblingAt(take(init(p), i + 1), r).v ;
                            { seqAppendIndexLemmas(init(p), [last(p)], i + 1) ; }
                            siblingAt(take(init(p) + [last(p)], i + 1), r).v ;
                            { seqLemmas(p); }
                            siblingAt(take(p, i + 1), r).v ;
                            v2[i];
                            //  because i < |v2| - 1 == |p| - 1, it does not matter if we omit last(v2).
                            init(v2)[i];
                            //  We can add anything at the end of init(v2) leaving value
                            //  at index i unchanged
                            { seqAppendIndexLemmas(init(v2), [last(v1)], i) ;}
                            (init(v2) + [last(v1)])[i];
                            computeLeftSiblingOnNextPath(p, v1, v2)[i];   
                        }
                    } else {
                        // i == |p| - 1
                        calc == {
                            siblingAt(take(nextPath(p), i + 1),r).v ;
                            // i == |p| - 1
                            { seqLemmas(nextPath(p)); }
                            siblingAt(nextPath(p), r).v ;
                            //  Definition of sibling
                            nodeAt(init(p) + [0], r).v;
                            //  init(p) + [0] == p
                            { seqLemmas(p); }
                            nodeAt(take(p, |p|), r).v;
                            // v1[|p| - 1];
                            last(v1);
                            //  by Req2
                            last(computeLeftSiblingOnNextPath(p, v1, v2)) ;
                        }
                    }
                } else {
                    // last(p) == 1
                    assert(last(p) == 1);
                    if ( i < |p| - 1 ) {
                        //  Induction on init(p), init(v1), init(v2)
                        //  Check pre conditions to apply lemma inductively
                       
                        //  Req2 on init(p) and init(v1)
                        forall (k : int | 0 <= k < |init(p)| ) 
                            ensures v1[k] ==  nodeAt(take(init(p), k + 1),r).v
                        {
                            calc == {
                                v1[k];
                                //  Req2
                                nodeAt(take(p, k + 1),r).v ;
                                { seqIndexLemmas(p, k + 1); }
                                nodeAt(take(init(p), k + 1), r).v ;
                            }
                        }

                        //  Req3 on init(p) and init(v2)
                        forall (k : int | 0 <= k < |init(p)| && init(p)[k] == 1 ) 
                            ensures v2[k] == siblingAt(init(p)[.. k + 1],r).v
                        {
                            calc == {
                                v2[k];  // show that p[k] == 1 and by Req3 on p, same as sibling.
                                calc ==> {
                                   init(p)[k] == 1;
                                    {   assert( k < |init(p)|); // pre-condition for seqLemmas(p,k)
                                        seqLemmas(p); }
                                    p[k] == 1;  
                                }
                                //  Req3 applies
                                siblingAt(take(p, k + 1),r).v ;
                                { seqIndexLemmas(p, k + 1); }
                                siblingAt(take(init(p),k + 1),r).v ;
                            }
                        }

                        //  Req1: existence of zero in init(p)
                        calc ==> {
                            exists j:: 0 <= j < |p|  && p[j] == 0;
                            last(p) != 0;
                            { pushExistsToInitPrefixIfNotLast(p); }
                            exists j:: 0 <= j < |init(p)|  && init(p)[j] == 0;
                        }

                        //  Induction hypothesis on init(p), init(v1), init(v2) 
                        calc == {
                            computeLeftSiblingOnNextPath(init(p), init(v1), init(v2))[i] ;
                            { computeLeftSiblingOnNextPathIsCorrect(init(p), r, init(v1), init(v2)); }
                            siblingAt(nextPath(init(p))[..i + 1],r).v;
                            {   //  pre-conditions for foo222(p, i + 1)
                                assert(0 <= i + 1 < |p|);
                                assert(|p| >= 2);
                                //  init(p) and p are the same upto |init(p)| and thus to i + 1
                                prefixOfNextPathOfInitIsSameIfLastisOne(p, i + 1); }
                            siblingAt(nextPath(p)[..i + 1],r).v;
                        }
                    } else {
                        //  i == |p| - 1 and nextpath(p)[|p| - 1] == 0 so trivially true
                        //  as nextpath(p)[|p| - 1] != 1
                        //  Thanks Dafny 
                    }
                }
            }
        }
    }
}