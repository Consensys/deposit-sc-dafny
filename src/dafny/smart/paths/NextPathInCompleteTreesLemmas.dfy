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

include "../trees/CompleteTrees.dfy"
include "../helpers/Helpers.dfy"
include "PathInCompleteTrees.dfy"
include "../seqofbits/SeqOfBits.dfy"
include "../helpers/SeqHelpers.dfy"
include "../trees/Trees.dfy"

module NextPathInCompleteTreesLemmas {

    import opened CompleteTrees
    import opened Helpers
    import opened PathInCompleteTrees
    import opened SeqOfBits
    import opened SeqHelpers
    import opened Trees 

    /**
     *  Next path from a leaf must go to the next leaf
     */
    lemma {:induction p, r} nextPathNextLeaf(p: seq<bit>, r :  Tree, k : nat) 
        requires isCompleteTree(r)                              
        requires hasLeavesIndexedFrom(r, 0)
        requires 1 <= |p| == height(r)                    
        requires 0 <= k < |leavesIn(r)| - 1                     
        requires nodeAt(p, r) == leavesIn(r)[k]                 
        ensures exists i ::  0 <= i < |p| && p[i] == 0          //  P1
        ensures  nodeAt(nextPath(p), r) == leavesIn(r)[k + 1]   //  P2
    {
        //  Proof of P1
        calc ==> {
            true;
            { pathToLeafInInitHasZero(p, r, k); }
            exists i ::  0 <= i < |p| && p[i] == 0;
        }

        //  Proof of P2
        //  We just need to prove that bitListToNat(nextpath(p)) == k + 1 
        calc == {
            bitListToNat(nextPath(p));
            //  bitListToNat(nextPath(p)) == bitListToNat(p) + 1
            {nextPathIsSucc(p); }
            bitListToNat(p) + 1;
            { indexOfLeafisIntValueOfPath(p, r, k); }
            // ==> bitListToNat(p) == k
            k + 1;
        }
        //  and apply indexOfLeafisIntValueOfPath
        indexOfLeafisIntValueOfPath(nextPath(p), r, k + 1);
    }

    /**
     *  Compute the left siblings of nextPath.
     *
     *  @param  p   A path.
     *  @param  v1  The values of the nodes on the path.
     *  @param  v2  The values of the nodes that are left siblings of nodes on the path.
     *  @returns    The values of the nodes that are left siblings of nextPath(p).
     */
    function method computeLeftSiblingOnNextPath<T>(p: seq<bit>, v1 : seq<T>, v2 : seq<T>) : seq<T>
        requires 1 <= |p| 
        requires |v1| == |v2| == |p|
        ensures |computeLeftSiblingOnNextPath(p, v1, v2)| == |v1|

        decreases p
    {
        if |p| == 1 then
            //  if p[0] == 0, we use v1, and otherwise p[0] == 1 we can choose
            //  whatever we want as at this level the sibling on next path is on
            //  the right. We choose to use v2 in order to enable optimisations
            //  in the imperative version of the algorithm
            if first(p) == 0 then v1 else v2 
        else 
            assert(|p| >= 2);
            if last(p) == 0 then 
                //  Next path is init(p) + [1]
                //  init(nextPath(p)_ is the same a\s init(p)  
                //  Hence the values on left siblings are in init(v2) and [last(v1)] 
                init(v2) + [last(v1)]
            else 
                assert(last(p) == 1);
                //  Nextpath is given as nextPath(init(p)) + [0]
                //  The last element is a zero, so the sibling on the last
                //  element is a right sibling and the value does not matter.
                //  We use last(v2) to allow for optimisations in the imperative version.
                computeLeftSiblingOnNextPath(init(p), init(v1), init(v2)) + [last(v2)]
    } 

    function method computeLeftSiblingOnNextPath2<T>(k: nat, h: nat, p: seq<bit>, v1 : seq<T>, v2 : seq<T>) : seq<T>
        requires 1 <= |p| == h
        requires k < power2(h) 
        requires |v1| == |v2| == |p|
        requires natToBitList2(k, h) == p
        ensures computeLeftSiblingOnNextPath2(k, h, p, v1, v2) == computeLeftSiblingOnNextPath(p, v1, v2)

        decreases p
    {
        if |p| == 1 then
            //  if p[0] == 0, we use v1, and otherwise p[0] == 1 we can choose
            //  whatever we want as at this level the sibling on next path is on
            //  the right. We choose to use v2 in order to enable optimisations
            //  in the imperative version of the algorithm
            if first(p) == 0 then v1 else v2 
        else 
            assert(|p| >= 2);
            if last(p) == 0 then 
            assert( k % 2 == 0);
            assert( h == |p|);
                //  Next path is init(p) + [1]
                //  init(nextPath(p)_ is the same a\s init(p)  
                //  Hence the values on left siblings are in init(v2) and [last(v1)] 
                init(v2) + [last(v1)]
            else 
                assert(last(p) == 1);
                assert( k % 2 == 1);
                assert( h == |p|);
                //  Nextpath is given as nextPath(init(p)) + [0]
                //  The last element is a zero, so the sibling on the last
                //  element is a right sibling and the value does not matter.
                //  We use last(v2) to allow for optimisations in the imperative version.
                computeLeftSiblingOnNextPath(init(p), init(v1), init(v2)) + [last(v2)]
    } 

    function method computeLeftSiblingOnNextPath3<T>(k: nat, h: nat, v1 : seq<T>, v2 : seq<T>) : seq<T>
        requires 1 <=  h
        requires k < power2(h) 
        requires |v1| == |v2| == h
        // requires natToBitList2(k, h) == p
        ensures computeLeftSiblingOnNextPath3(k, h, v1, v2) 
                == var p := natToBitList(k, h);
                    computeLeftSiblingOnNextPath2(k, h, p, v1, v2)
        decreases h
    {
        if h == 1 then
            //  if p[0] == 0, we use v1, and otherwise p[0] == 1 we can choose
            //  whatever we want as at this level the sibling on next path is on
            //  the right. We choose to use v2 in order to enable optimisations
            //  in the imperative version of the algorithm
            if k % 2 == 0 then v1 else v2 
        else 
            // assert(|p| >= 2);
            if k % 2 == 0 then 
            // assert( k % 2 == 0);
            // assert( h == |p|);
                //  Next path is init(p) + [1]
                //  init(nextPath(p)_ is the same a\s init(p)  
                //  Hence the values on left siblings are in init(v2) and [last(v1)] 
                init(v2) + [last(v1)]
            else 
                // assert(last(p) == 1);
                // assert( k % 2 == 1);
                // assert( h == |p|);
                //  Nextpath is given as nextPath(init(p)) + [0]
                //  The last element is a zero, so the sibling on the last
                //  element is a right sibling and the value does not matter.
                //  We use last(v2) to allow for optimisations in the imperative version.
                computeLeftSiblingOnNextPath3(k / 2, h - 1, init(v1), init(v2)) + [last(v2)]
    } 

     function method computeLeftSiblingOnNextPath4<T>(k: nat, k' : nat, h: nat, v1 : seq<T>, v2 : seq<T>) : seq<T>
        requires 1 <=  h
        requires k + 1 == k' < power2(h) 
        requires |v1| == |v2| == h
        // requires natToBitList2(k, h) == p
        ensures computeLeftSiblingOnNextPath4(k, k', h, v1, v2) 
                == computeLeftSiblingOnNextPath3(k, h, v1, v2)
        decreases h
    {
        if h == 1 then
            //  if p[0] == 0, we use v1, and otherwise p[0] == 1 we can choose
            //  whatever we want as at this level the sibling on next path is on
            //  the right. We choose to use v2 in order to enable optimisations
            //  in the imperative version of the algorithm
            assert(k' % 2 == 1 <==> k % 2 == 0);
            if k % 2 == 0 then v1 else v2 
        else 
            assert(k' % 2 == 1 <==> k % 2 == 0);
            // assert(|p| >= 2);
            if k % 2 == 0 then 
            // assert( k % 2 == 0);
            // assert( h == |p|);
                //  Next path is init(p) + [1]
                //  init(nextPath(p)_ is the same a\s init(p)  
                //  Hence the values on left siblings are in init(v2) and [last(v1)] 
                init(v2) + [last(v1)]
            else 
                // assert(last(p) == 1);
                // assert( k % 2 == 1);
                // assert( h == |p|);
                //  Nextpath is given as nextPath(init(p)) + [0]
                //  The last element is a zero, so the sibling on the last
                //  element is a right sibling and the value does not matter.
                //  We use last(v2) to allow for optimisations in the imperative version.
                computeLeftSiblingOnNextPath4(k / 2, k' / 2, h - 1, init(v1), init(v2)) + [last(v2)]
    } 

    function method computeLeftSiblingOnNextPath5<T>(k: nat, k' : nat, h: nat, v1 : seq<T>, v2 : seq<T>) : seq<T>
        requires 1 <=  h
        requires k + 1 == k' < power2(h) 
        requires |v1| == |v2| == h
        // requires natToBitList2(k, h) == p
        ensures computeLeftSiblingOnNextPath5(k, k', h, v1, v2) 
                == computeLeftSiblingOnNextPath4(k, k', h, v1, v2)
        decreases h
    {
        if h == 1 then
            //  if p[0] == 0, we use v1, and otherwise p[0] == 1 we can choose
            //  whatever we want as at this level the sibling on next path is on
            //  the right. We choose to use v2 in order to enable optimisations
            //  in the imperative version of the algorithm
            assert(k' % 2 == 1 <==> k % 2 == 0);
            if k' % 2 == 1 then v1 else v2 
        else 
            assert(k' % 2 == 1 <==> k % 2 == 0);
            // assert(|p| >= 2);
            if k' % 2 == 1 then 
            // assert( k % 2 == 0);
            // assert( h == |p|);
                //  Next path is init(p) + [1]
                //  init(nextPath(p)_ is the same a\s init(p)  
                //  Hence the values on left siblings are in init(v2) and [last(v1)] 
                init(v2) + [last(v1)]
            else 
                // assert(last(p) == 1);
                // assert( k % 2 == 1);
                // assert( h == |p|);
                //  Nextpath is given as nextPath(init(p)) + [0]
                //  The last element is a zero, so the sibling on the last
                //  element is a right sibling and the value does not matter.
                //  We use last(v2) to allow for optimisations in the imperative version.
                computeLeftSiblingOnNextPath4(k / 2, k' / 2, h - 1, init(v1), init(v2)) + [last(v2)]
    } 


    /** 
     *  This is the deposit smart contract version using k + 1 (deposit_count + 1).
     */
    function method computeLeftSiblingOnNextPath6<T>(k: nat, h: nat, v1 : seq<T>, v2 : seq<T>) : seq<T>
        requires 1 <=  h
        requires 1 <= k < power2(h) 
        requires |v1| == |v2| == h
        
        ensures computeLeftSiblingOnNextPath6(k, h, v1, v2) 
            == computeLeftSiblingOnNextPath5(k - 1, k , h, v1, v2)
            == computeLeftSiblingOnNextPath3(k - 1, h, v1, v2)
            == var p := natToBitList(k - 1, h);
                    computeLeftSiblingOnNextPath2(k - 1, h, p, v1, v2)

        decreases h
    {
        if h == 1 then
            //  if p[0] == 0, we use v1, and otherwise p[0] == 1 we can choose
            //  whatever we want as at this level the sibling on next path is on
            //  the right. We choose to use v2 in order to enable optimisations
            //  in the imperative version of the algorithm
            // assert(k % 2 == 1 <==> k % 2 == 0);
            if k % 2 == 1 then v1 else v2 
        else 
            // assert(k % 2 == 1 <==> k % 2 == 0);
            // assert(|p| >= 2);
            if k % 2 == 1 then 
            // assert( k % 2 == 0);
            // assert( h == |p|);
                //  Next path is init(p) + [1]
                //  init(nextPath(p)_ is the same a\s init(p)  
                //  Hence the values on left siblings are in init(v2) and [last(v1)] 
                init(v2) + [last(v1)]
            else 
                // assert(last(p) == 1);
                // assert( k % 2 == 1);
                // assert( h == |p|);
                //  Nextpath is given as nextPath(init(p)) + [0]
                //  The last element is a zero, so the sibling on the last
                //  element is a right sibling and the value does not matter.
                //  We use last(v2) to allow for optimisations in the imperative version.
                computeLeftSiblingOnNextPath6(k / 2, h - 1, init(v1), init(v2)) + [last(v2)]
    } 

    

    /**
     *  computeLeftSiblingOnNextPath returns values on left siblings of next path.
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
                    //  next path must end with 1 and hence p[|p| - 1] == 0
                    // assert(nextPath(p) == p[..|p| - 1] + [1]);
                    calc == {
                        nextPath(p);
                        init(p) + [1];
                    }
                    // assert(p[|p| - 1] == 0);
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
                            //  i < |v2| - 1 == |p| - 1
                            init(v2)[i];
                            //  we can add anything at the end of init(v2) leaving value
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
                            //  Def of sibling
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