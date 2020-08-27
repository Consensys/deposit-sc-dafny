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
        requires isCompleteTree(r)                              // 1.
        requires hasLeavesIndexedFrom(r, 0)
        requires 1 <= |p| == height(r) - 1                      // 2.
        requires 0 <= k < |leavesIn(r)| - 1                     // 3.
        requires nodeAt(p, r) == leavesIn(r)[k]                 // 4.
        ensures exists i ::  0 <= i < |p| && p[i] == 0          //  P1
        ensures  nodeAt(nextPath(p), r) == leavesIn(r)[k + 1]   //  P2
    {
        //  proof of P1
        pathToLeafInInitHasZero(p, r, k);
        //   proof of P2
        nextPathIsSucc(p);
        assert(bitListToNat(nextPath(p)) == bitListToNat(p) + 1);
        indexOfLeafisIntValueOfPath(p, r, k);
        assert(bitListToNat(p) == k);
        assert(bitListToNat(nextPath(p)) == k + 1);
        indexOfLeafisIntValueOfPath(nextPath(p), r, k + 1);
    }

    /**
     *  Left siblings of nextPath(p) are either nodes of p or
     *  left siblings of p.
     */
    // lemma {:induction p, r} leftSiblingAtNextPathOnPathOrSiblingOfPath(p: seq<bit>, r :  Tree, k : nat)
    //     requires isCompleteTree(r)      
    //     requires hasLeavesIndexedFrom(r, 0)                        
    //     requires 1 <= |p| == height(r) - 1                      
    //     requires 0 <= k < |leavesIn(r)| - 1                     
    //     requires nodeAt(p, r) == leavesIn(r)[k]                 

    //     ensures (exists i ::  0 <= i < |p| && p[i] == 0)
    //             &&
    //             forall i :: 0 <= i < |p| && nextPath(p)[i] == 1 ==> 
    //                 (
    //                     siblingAt(nextPath(p)[..i + 1], r) == nodeAt(p[..i + 1], r)
    //                     ||
    //                     siblingAt(nextPath(p)[..i + 1], r) == siblingAt(p[..i + 1], r)
    //                 )
    // {
    //    pathToLeafInInitHasZero(p, r , k) ;
    //    foo32(p, r);
    // }

    /**
     *  Left siblings of nextPath are on path or are sibling of path.
     *  This lemma does not seem to be used anywhere.
     */
    lemma {:induction p, r} foo32a(p: seq<bit>, r :  Tree)
        requires isCompleteTree(r)                              
        requires 1 <= |p| <= height(r) - 1                      
        requires exists i ::  0 <= i < |p| && p[i] == 0
        ensures (
                forall i :: 0 <= i < |p| 
                    && nextPath(p)[i] == 1 ==> 
                    (
                        siblingAt(nextPath(p)[..i + 1], r) == nodeAt(p[..i + 1], r)
                        ||
                        siblingAt(nextPath(p)[..i + 1], r) == siblingAt(p[..i + 1], r)
                    )
        )
        decreases p
    {
        if |p| == 1 {
            forall( i : int | 0 <= i < |p| && nextPath(p)[i] == 1) 
                ensures 
                    (
                        siblingAt(nextPath(p)[..i + 1], r) == nodeAt(p[..i + 1], r)
                        ||
                        siblingAt(nextPath(p)[..i + 1], r) == siblingAt(p[..i + 1], r) 
                    )
            {
                assert(p[0] == 0) ;
                assert(nextPath(p) == [1]);
                calc == {
                    siblingAt(nextPath(p)[..i + 1], r);
                    siblingAt(nextPath(p)[..0 + 1], r);
                    siblingAt(nextPath(p), r);
                    siblingAt([1], r);
                    nodeAt(p[..0] + [0], r);
                    nodeAt(p[..i + 1], r);
                }
            }

        } else {
            forall( i : int | 0 <= i < |p| && nextPath(p)[i] == 1) 
                ensures 
                    (
                        siblingAt(nextPath(p)[..i + 1], r) == nodeAt(p[..i + 1], r)
                        ||
                        siblingAt(nextPath(p)[..i + 1], r) == siblingAt(p[..i + 1], r) 
                    )
            {
                if p[|p| - 1] == 0 {
                    assert(nextPath(p) == p[..|p| - 1] + [1]);
                    //  as nextpath == p[..|p| - 1] + [1], split into i < |p| - 1 and last i
                    if ( i < |p| - 1) {
                        calc == {
                            siblingAt(nextPath(p)[..i + 1], r);
                            //  in that case the path is the same as p[..i] and so is sibling
                            == calc == {
                                nextPath(p)[.. i + 1];
                                ==
                                p[.. i + 1] ;
                            }
                            siblingAt(p[..i + 1], r);
                        }
                    } else {
                        //  i == |p| - 1
                        calc == {
                            siblingAt(nextPath(p)[..i + 1], r) ;
                            ==
                            siblingAt(nextPath(p)[..|p|], r);
                            ==
                            siblingAt((p[..|p| - 1] + [1])[..|p|], r);
                            == { foo000(p, 1); }
                            siblingAt((p[..|p| - 1] + [1]), r);
                            == //{ foo900(p[..|p| - 1], r, 1);}
                            nodeAt(p[..|p| - 1] + [0], r);
                            == calc == {
                                p[..|p| - 1] + [0] ;
                                ==
                                p[..|p|];
                            }
                            nodeAt(p[..i + 1], r);
                        }
                    }
                } else {
                    //  p[|p| - 1] == 1
                    // nextPath(p[.. |p| - 1]) + [0]
                    //  Split into induction on p[..|p| - 1] and last node
                     //  ensure nextPath pre-conds are satisfied
                    // foo450(p, r, k);
                   

                    if ( i < |p| - 1) {
                        //  induction on p[..|p| - 1]
                        foo32a(p[.. |p| - 1], r);

                        assert(siblingAt(nextPath(p[.. |p| - 1 ])[..i + 1], r) == nodeAt(p[..|p| - 1][..i + 1], r)
                        ||
                        siblingAt(nextPath(p[.. |p| - 1])[..i + 1], r) == siblingAt(p[.. |p| - 1][..i + 1], r) 
                        );
                        assert(p[.. |p| - 1][..i + 1] == p[..i + 1]);
                        assert(nextPath(p)[.. i + 1] == nextPath(p[.. |p| - 1 ])[..i + 1]);

                        assert(siblingAt(nextPath(p[.. |p| - 1 ])[..i + 1], r) == nodeAt(p[..i + 1], r)
                        ||
                        siblingAt(nextPath(p[.. |p| - 1])[..i + 1], r) == siblingAt(p[..i + 1], r) 
                        );
                    } else {
                        //  Thanks Dafny
                    }
                }
            }
        }
    }

    lemma foo000<T>(s : seq<T>, a : T) 
        requires |s| >= 1
        ensures (s[.. |s| - 1] + [a])[..|s|] ==  s[.. |s| - 1] + [a]
    {}

    /**
     *  Compute the left siblings of nextPath.
     *
     *  @param  p   A path.
     *  @param  v1  The values of the nodes on the path.
     *  @param  v2  The values of the nodes that are left siblings of nodes on the path.
     *  @returns    The values of the nodes that are left siblings of nextPath(p).
     */
    function method computeLeftSiblingOnNextPath<T>(p: seq<bit>, v1 : seq<T>, v2 : seq<T>) : seq<T>
        // requires isCompleteTree(r)                              
        requires 1 <= |p| 
        // <= height(r) - 1      
        // requires exists i :: 0 <= i < |p| && p[i] == 0
        requires |v1| == |v2| == |p|
        // requires forall i :: 0 <= i < |p| ==>
            // v1[i] == nodeAt(p[.. i + 1],r).v 
        // requires forall i :: 0 <= i < |p| ==>
            // p[i] == 1 ==> v2[i] == siblingAt(p[.. i + 1],r).v 

        ensures |computeLeftSiblingOnNextPath(p, v1, v2)| == |v1|

        decreases p
    {
        if |p| == 1 then
            //  does not really matter as we'll use it only with p[0] == 0 and
            //  in that case we want v1
            // assert(p[0] == 0);
            if p[0] == 0 then v1 else v2 
        else 
            // assert(|p| >= 2);
            if p[|p| - 1] == 0 then 
                //  Next path is p[..|p| - 1] + [1]
                //  nextPath(p) and p agree on first |p| - 1 steps 
                //  Collect values from v2[..|p| - 1 ] and add value at NodeAt(p,r)
                v2[..|p| - 1] + [v1[|p| - 1 ]]
            else 
                //  Nextpath is nextPath(p[.. |p| - 1]) + [0]
                //  p[|p| - 1] == 0, next path will lead to another branch from ancestor
                //  At that level in the tree nextPath(p)[|p| - 1] == 0 so whatever is good
                // assert(forall i {:trigger p[.. i + 1]} :: 0 <= i < |p| - 1 ==>
                        // p[.. i + 1] == p[..|p| - 1][.. i + 1]);

                computeLeftSiblingOnNextPath(p[.. |p| - 1], v1[..|p| - 1], v2[..|p| - 1]) + [v2[|p| - 1 ]]
    } 

    /**
     *  computeLeftSiblingOnNextPath returns values on left siblings of next path.
     */
    lemma {:induction p, v1, v2} computeOnNextPathCollectsValuesOfNextLeftSiblings<T>(p: seq<bit>, r :  Tree<T>, v1 : seq<T>, v2 : seq<T>)
        requires isCompleteTree(r)                              
        requires 1 <= |p| <= height(r) - 1      

        requires exists i :: 0 <= i < |p| && p[i] == 0  //  Req1
        requires |v1| == |v2| == |p|
        requires forall i :: 0 <= i < |p| ==>           //  Req2
            v1[i] == nodeAt(p[.. i + 1],r).v 
        requires forall i :: 0 <= i < |p| ==>           //  Req3 
            p[i] == 1 ==> v2[i] == siblingAt(p[.. i + 1],r).v 

        ensures forall i :: 0 <= i < |p| && nextPath(p)[i] == 1 ==> 
                computeLeftSiblingOnNextPath(p, v1, v2)[i] == siblingAt(nextPath(p)[..i + 1],r).v

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
                    nodeAt(p[..1],r).v;
                    nodeAt([0],r).v;
                    nodeAt([1][..0] + [0],r).v;
                    siblingAt([1],r).v;
                    siblingAt(nextPath(p)[..i + 1],r).v;
                }
            } else {
                //  |p| >= 2
                if (last(p) == 0) {
                    //  next path must end with 1 and hence p[|p| - 1] == 0
                    assert(nextPath(p) == p[..|p| - 1] + [1]);
                    assert(p[|p| - 1] == 0);
                    if ( i < |p| - 1 ) {
                        //  nextpath prefix is prefix of p
                        calc == {
                            siblingAt(nextPath(p)[..i + 1],r).v ;
                            == calc == {
                                nextPath(p)[..i + 1];
                                p[.. i + 1];
                            }
                            siblingAt(p[.. i + 1], r).v ;
                            v2[i];
                            v2[..|p| - 1][i];
                            (v2[..|p| - 1] + [v1[|p| - 1 ]])[i];
                            computeLeftSiblingOnNextPath(p, v1, v2)[i];
                        }
                    } else {
                        // i == |p| - 1
                        calc == {
                            siblingAt(nextPath(p)[..i + 1],r).v ;
                            == calc == {
                                i + 1;
                                |p|;
                            }
                            siblingAt(nextPath(p)[..|p|],r).v ;
                            calc == {
                                nextPath(p)[..|p|];
                                nextPath(p);
                            }
                            siblingAt(nextPath(p),r).v;
                            nodeAt(p[..|p| - 1] + [0], r).v;
                            == calc == {
                                p ;
                                {seqLemmas(p);}
                                p[..|p| - 1] + [0];
                            }
                            nodeAt(p, r).v;
                            == calc == {
                                p ;
                                p[..|p| + 1 - 1];
                            }
                            nodeAt(p[.. |p| + 1 - 1],r).v;
                            v1[|p| - 1];
                            computeLeftSiblingOnNextPath(p, v1, v2)[|p| - 1] ;
                            == calc == {
                                i ;
                                |p| - 1;
                            }
                            computeLeftSiblingOnNextPath(p, v1, v2)[i] ;
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
                            { computeOnNextPathCollectsValuesOfNextLeftSiblings(init(p), r, init(v1), init(v2)); }
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