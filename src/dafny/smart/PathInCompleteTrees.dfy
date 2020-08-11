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

include "Trees2.dfy"
include "CompleteTrees.dfy"
include "SeqOfBits.dfy"
include "Helpers.dfy"
include "SeqHelpers.dfy"

module PathInCompleteTrees {

    import opened Trees 
    import opened CompleteTrees
    import opened SeqOfBits
    import opened Helpers
    import opened SeqHelpers

    /**
     *  The node at the end of a path.
     *
     *  @param  p   A path (left/right) in a binary tree.
     *  @param  r   A complete binary tree.
     *
     *  @returns    The node of the tree that is the target of path `p`.
     */
    function nodeAt(p : seq<bit>, r: ITree) : ITree
        requires |p| < height(r) 
        requires isCompleteTree(r)
        ensures nodeAt(p, r) in nodesIn(r)
        decreases p
    {
        if |p| == 0 then  
            r
        else 
            // r must be a node as height(r) > |p| >= 1
            match r 
                case INode(_, lc, rc, _) => 
                    nodeAt(p[1..], if p[0] == 0 then lc else rc)
    }

    /**
     *  The siblings (left or roght) of each node (except root) on the path.
     */
    function siblingAt(p : seq<bit>, r :ITree) : ITree
        requires 1 <= |p| < height(r) 
        requires isCompleteTree(r)
        decreases p
    {
        if |p| == 1 then
            match r 
                case INode(_, lc, rc, _) =>
                    if p[0] == 0 then rc
                    else lc
        else 
            match r 
                case INode(_, lc, rc, _) => 
                    if p[0] == 0 then 
                        siblingAt(p[1..], lc)
                    else 
                        siblingAt(p[1..], rc)
    }

    function siblingAt2(p : seq<bit>, r :ITree) : ITree
        requires 1 <= |p| < height(r) 
        requires isCompleteTree(r)
    {
        if p[|p| - 1] == 0 then
            nodeAt(p[..|p| - 1] + [1], r)
        else
            nodeAt(p[..|p| - 1] + [0], r)
    }

    lemma foo900(p : seq<bit>, r :ITree, a : bit) 
        requires 0 <= |p| < height(r) - 1
        requires isCompleteTree(r)
        ensures siblingAt(p + [a], r) == nodeAt(p + [1 - a], r)      
    {
        if |p| == 0 {
            //  Thanks Dafny
        } else {
            match r 
                case INode(_, lc, rc, _) =>
                    if p[0] == 0 {
                        assert(nodeAt(p + [a], r) == nodeAt((p + [a])[1..], lc));
                        assert((p + [1 - a])[1..] == p[1..] + [1 - a]);
                        calc {
                            siblingAt(p + [a], r) ;
                            ==
                            siblingAt((p + [a])[1..], lc);
                            == calc == {    //  These terms are equal
                                (p + [a])[1..] ;
                                p[1..] + [a];
                            }
                            siblingAt((p[1..] + [a]), lc);
                            ==
                            nodeAt(p[1..] + [1 - a], lc) ;
                            ==
                            nodeAt(p + [1 - a] , r);
                        }
                    } else {
                        assert(nodeAt(p + [a], r) == nodeAt((p + [a])[1..], rc));
                        assert((p + [1 - a])[1..] == p[1..] + [1 - a]);
                        calc {
                            siblingAt(p + [a], r) ;
                            ==
                            siblingAt((p + [a])[1..], rc);
                            == calc {
                                (p + [a])[1..] ;
                                ==
                                p[1..] + [a];
                            }
                            siblingAt((p[1..] + [a]), rc);
                            ==
                            nodeAt(p[1..] + [1 - a], rc) ;
                            ==
                            nodeAt(p + [1 - a] , r);
                        }
                    }
        }
    }  

    lemma foo901(p : seq<bit>, r :ITree) 
        requires 1 <= |p| < height(r) 
        requires isCompleteTree(r)
        
        ensures height(nodeAt(p, r)) == height(r) - |p| 
        // && nodeAt(p + [0], r) == nodeAt([0], nodeAt(p, r))
    { }

    lemma foo902(p : seq<bit>, r :ITree, a : bit) 
        requires 1 <= |p| < height(r) - 1
        requires isCompleteTree(r)
        
        ensures height(nodeAt(p, r)) == height(r) - |p| 
            && isCompleteTree(nodeAt(p, r))
            && nodeAt(p + [a], r) == nodeAt([a], nodeAt(p, r))
            // && nodeAt(p + [1], r) == nodeAt([1], nodeAt(p, r))
    { 
        foo901(p, r) ;
        if |p| == 1 {
            //  Thanks Dafny
        } else {
            match r 
                case INode(_, lc, rc, _) => 
                if p[0] == 0 {
                    calc == {
                        nodeAt(p + [a], r);
                        ==
                        nodeAt((p + [a])[1..], lc);
                        == calc {
                            (p + [a])[1..] ;
                            ==
                            p[1..] + [a];
                        }
                        nodeAt(p[1..] + [a], lc);

                    }
                } else {
                    calc == {
                        nodeAt(p + [a], r);
                        ==
                        nodeAt((p + [a])[1..], rc);
                        == calc {
                            (p + [a])[1..] ;
                            ==
                            p[1..] + [a];
                        }
                        nodeAt(p[1..] + [a], rc);
                }
            }
        }
    }

   
    lemma nodeLoc(r : ITree, p : seq<bit>) 
        requires 1 <= |p| == height(r) - 1
        requires isCompleteTree(r)

        ensures match r 
            case INode(_, lc, rc, _) =>
                p[0] == 0 ==> nodeAt(p, r) in leavesIn(lc)
                &&
                p[0] == 1 ==> nodeAt(p, r) in leavesIn(rc)

    lemma nodeLoc2(r : ITree, p : seq<bit>, k : nat) 
        requires 1 <= |p| == height(r) - 1
        requires isCompleteTree(r)
        // requires isValidIndex(r, p')
        requires k < power2(height(r) - 1)
        requires k < |leavesIn(r)|
        // requires nodeAt(p, r).id == leavesIn(r)[k].id
        // requires p' + p == leavesIn(r)[k].id
        // requires nodeAt(p, r) == leavesIn(r)[k]

        ensures match r 
            case INode(_, lc, rc, _) =>
                (p[0] == 0 && k < power2(height(r) - 1)/2)
                ||
                (p[0] == 1 && k >= power2(height(r) - 1)/2)


    lemma foo302(p : seq<bit>, r : ITree, k : nat) 
        requires isCompleteTree(r)
        requires 1 <= |p| == height(r) - 1 
        requires k < |leavesIn(r)|
        requires nodeAt(p, r) == leavesIn(r)[k]
        ensures bitListToNat(p) == k
    {
        if |p| == 1 {
            if p[0] == 0 {
                nodeLoc2(r, p, k);
                assert(k == 0);
                assert(bitListToNat(p) == 0);
                assert(nodeAt(p, r) == leavesIn(r)[0]);
            } else {
                assert(p[0] == 1);
                nodeLoc2(r, p, k);
                assert(k == 1);
                assert(bitListToNat(p) == 1);
                assert(nodeAt(p, r) == leavesIn(r)[k]);
            }
        } else {
            //  r is not a leaf
            match r 
                case INode(_, lc, rc, _) => 
                    if p[0] == 0 {
                        //  left lc
                        assert(nodeAt(p, r) == nodeAt(p[1..], lc));
                        //  HI on rc
                        completeTreesLeftRightHaveSameNumberOfLeaves(r);
                        nodeLoc2(r, p, k);
                        assert( k < power2(height(r) - 1)/ 2);
                        assert(|leavesIn(lc)| == power2(height(r) - 1)/ 2);
                        // foo302(p[1..], lc, k);
                    } else {
                        //  p[0] == 1
                        assert(nodeAt(p, r) == nodeAt(p[1..], rc));
                        completeTreesLeftRightHaveSameNumberOfLeaves(r);
                        nodeLoc2(r, p, k);
                        assert( k >= power2(height(r) - 1)/ 2);
                        assert(|leavesIn(rc)| == power2(height(r) - 1)/ 2);
                        var k' := k - power2(height(r) - 1)/ 2 ;
                        foo302(p[1..], rc, k');
                    }
        }
    }

     lemma foo203(p : seq<bit>, r : ITree, k : nat) 
        requires isCompleteTree(r)
        requires 1 <= |p| == height(r) - 1 
        requires k < |leavesIn(r)|
        requires bitListToNat(p) == k
        ensures nodeAt(p, r) == leavesIn(r)[k]
        decreases p 
    {
        if |p| == 1 {
            if p[0] == 0 {
                nodeLoc2(r, p, k);
                assert(k == 0);
                assert(bitListToNat(p) == 0);
                assert(nodeAt(p, r) == leavesIn(r)[0]);
            } else {
                assert(p[0] == 1);
                nodeLoc2(r, p, k);
                assert(k == 1);
                assert(bitListToNat(p) == 1);
                assert(nodeAt(p, r) == leavesIn(r)[k]);
            }
        } else {
            //  r is not a leaf
            match r 
                case INode(_, lc, rc, _) => 
                    if p[0] == 0 {
                        //  left lc
                        assert(nodeAt(p, r) == nodeAt(p[1..], lc));
                        //  HI on rc
                        completeTreesLeftRightHaveSameNumberOfLeaves(r);
                        nodeLoc2(r, p, k);
                        assert( k < power2(height(r) - 1)/ 2);
                        assert(|leavesIn(lc)| == power2(height(r) - 1)/ 2);
                        // foo302(p[1..], lc, k);
                    } else {
                        //  p[0] == 1
                        assert(nodeAt(p, r) == nodeAt(p[1..], rc));
                        completeTreesLeftRightHaveSameNumberOfLeaves(r);
                        nodeLoc2(r, p, k);
                        assert( k >= power2(height(r) - 1)/ 2);
                        assert(|leavesIn(rc)| == power2(height(r) - 1)/ 2);
                        var k' := k - power2(height(r) - 1)/ 2 ;
                        foo203(p[1..], rc, k');
                        // assume( nodeAt(p, r) == leavesIn(r)[k]);
                    }
        }
    }

     lemma foo200(p : seq<bit>, r : ITree, k : nat) 
        requires isCompleteTree(r)
        requires 1 <= |p| == height(r) - 1 
        requires k < |leavesIn(r)|
        ensures bitListToNat(p) == k <==> nodeAt(p, r) == leavesIn(r)[k]
    {
        if (bitListToNat(p) == k) {
            foo203(p, r, k);
        } else if ( nodeAt(p, r) == leavesIn(r)[k]) {
            foo302(p, r, k);
        }
        
    }

    /**
     *  A path to a leaf of index < |leavesin{r)| -1 has a zero in it.
     */
    lemma {:induction p} pathToLeafInInitHasZero(p: seq<bit>, r : ITree, k : nat)
        requires |p| == height(r) - 1
        requires isCompleteTree(r)
        requires k < |leavesIn(r)| - 1
        requires nodeAt(p, r) == leavesIn(r)[k]
        ensures exists i :: 0 <= i < |p| && p[i] == 0
        decreases p 
    {
        if |p| == 1 {
            //  k < |leavesIn(r)| <==> k < 1 <==> k == 0, apply nodeLoc2 ==> p[0] == 0
            nodeLoc2(r, p, k);
        } else {
            if p[0] == 0 {
                //  p[0] is a witness
            } else {
                //  r is a node (not a leaf) and path leads to a node in rc
                match r
                    case INode(_, lc, rc, _) =>
                        completeTreeNumberLemmas(r);
                        assert(|leavesIn(r)| == power2(height(r) - 1));
                        assert( k < power2(height(r) - 1));
                        //  k >= power2(height(r) -1 ) /2 by
                        nodeLoc2(r, p, k);
                        //  leavesIn(r)[k] == leavesIn(rc)[k - power2(height(r) - 1)/2]
                        completeTreesLeftRightChildrenLeaves(r, height(r));
                        var k' := k - power2(height(r) - 1) / 2;
                        assert(leavesIn(r)[k] == leavesIn(rc)[k']);
                        completeTreesLeftRightHaveSameNumberOfLeaves(r);
                        //  induction on rc
                        pathToLeafInInitHasZero(p[1..], rc, k');
            }
        }
    }

    /**
     *  A path to a leaf which is not the rightmost one must have 
     *  a zero.
     */
    lemma {:induction p} foo450(p: seq<bit>, r : ITree, k : nat) 
        requires isCompleteTree(r)
        requires 1 <= |p| == height(r) - 1
        requires 0 <= k < |leavesIn(r)| - 1
        requires nodeAt(p, r) == leavesIn(r)[k]
        ensures  exists i ::  0 <= i < |p| && p[i] == 0 
        decreases p 
    {
        if |p| == 1 {
            //  Thanks Dafny
            assert(k == 0);
            nodeLoc2(r, p, k);
            assert(p[0] == 0);
        } else {
            if p[0] == 0 {
                //  
            } else {
                // p[0] == 1, apply to rc
                match r
                    case INode(_, _, rc, _) =>
                        assert(isCompleteTree(rc));
                        assert(1 <= |p[1..]|);
                        assert(nodeAt(p, r) == nodeAt(p[1..], rc));
                        // assert(|leavesIn(rc)| == )
                        completeTreesLeftRightHaveSameNumberOfLeaves(r);
                        assert(p[0] == 1);
                        nodeLoc2(r, p, k);
                        assert( 0 <= k - power2(height(r) - 1) / 2);
                        assert( k - power2(height(r) - 1)/ 2 < |leavesIn(rc)| - 1);
                        foo450(p[1..], rc, k - power2(height(r) - 1)/2);
                        assert(exists i ::  0 <= i < |p[1..]| && p[1..][i] == 0); 
                        // var i :|  0 <= i < |p[1..]| && p[1..][i] == 0 ;
            }
        }
    } 

    // lemma foo201(p: seq<bit>, r : ITree, k : nat )
    //     requires isCompleteTree(r)
    //     requires 2 <= |p| == height(r) - 1
    //     requires 0 <= k < (|leavesIn(r)| - 1)/2 - 1
    //     requires nodeAt(p, r) == leavesIn(r)[k]
    //     // ensures  exists i ::  0 <= i < |p| && p[i] == 0 
    //     decreases p 
    //     ensures exists i ::  0 <= i < |p| && p[i] == 0 
    //     ensures match r 
    //         case INode(_, lc, rc, _) =>
    //             (exists i ::  0 <= i < |p| && p[i] == 0 )
    //             && nodeAt(nextPath(p), r) == nodeAt(nextPath(p[1..]), lc)
    // {
    //     foo450(p, r, k);
    //     if |p| == 2 {
    //         //  
    //     } else {

    //     }
    // }

    /**
     *  Next path from a leaf must go to the next leaf
     */
     lemma {:induction r} nextPathNextLeaf(p: seq<bit>, r : ITree, k : nat) 
        requires isCompleteTree(r)                              // 1.
        requires 1 <= |p| == height(r) - 1                      // 2.
        requires 0 <= k < |leavesIn(r)| - 1                     // 3.
        requires nodeAt(p, r) == leavesIn(r)[k]                 // 4.
        ensures exists i ::  0 <= i < |p| && p[i] == 0          //  P1
        ensures  nodeAt(nextPath(p), r) == leavesIn(r)[k + 1]   //  P2
    {
        //  proof of P1
        foo450(p, r, k);
        //   proof of P2
        nextPathIsSucc(p);
        assert(bitListToNat(nextPath(p)) == bitListToNat(p) + 1);
        foo200(p, r, k);
        assert(bitListToNat(p) == k);
        assert(bitListToNat(nextPath(p)) == k + 1);
        foo200(nextPath(p), r, k + 1);


    }

    lemma foo707(p: seq<bit>, r : ITree, k : nat)
        requires isCompleteTree(r)                              
        requires 1 <= |p| == height(r) - 1                      
        requires 0 <= k < |leavesIn(r)| - 1                     
        requires nodeAt(p, r) == leavesIn(r)[k]                 

        ensures (exists i ::  0 <= i < |p| && p[i] == 0)
                &&
                forall i :: 0 <= i < |p| && nextPath(p)[i] == 1 ==> 
                    (
                        siblingAt(nextPath(p)[..i + 1], r) == nodeAt(p[..i + 1], r)
                        ||
                        siblingAt(nextPath(p)[..i + 1], r) == siblingAt(p[..i + 1], r)
                    )
    {
       foo450(p, r , k) ;
       foo707b(p, r);
    }

     lemma foo707b(p: seq<bit>, r : ITree)
        requires isCompleteTree(r)                              
        requires 1 <= |p| <= height(r) - 1                      
        // requires 0 <= k < |nodesIn(r)| - 1                     
        // requires nodeAt(p, r) == nodesIn(r)[k]                 
        requires exists i ::  0 <= i < |p| && p[i] == 0
        ensures (
                forall i :: 0 <= i < |p| 
                    // && exists i ::  0 <= i < |p| && p[i] == 0
                    && nextPath(p)[i] == 1 ==> 
                    (
                        siblingAt(nextPath(p)[..i + 1], r) == nodeAt(p[..i + 1], r)
                        ||
                        siblingAt(nextPath(p)[..i + 1], r) == siblingAt(p[..i + 1], r)
                    )
        )
    {
        if |p| == 1 {
            //  Thanks Dafny
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
                            == { foo900(p[..|p| - 1], r, 1);}
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
                    assert(p[|p| - 1] == 1);
                    assert(exists i ::  0 <= i < |p| - 1  && p[i] == 0 );
                    // assert(p[.. |p| - 1] == )
                    assert(exists i ::  0 <= i < |p[.. |p| - 1]|   && p[.. |p| - 1][i] == 0 );

                    if ( i < |p| - 1) {
                        //  induction on p[..|p| - 1]
                        foo707b(p[.. |p| - 1], r);

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

    function method computeLeftSiblingOnNextPath<T>(p: seq<bit>, r : ITree<T>, v1 : seq<T>, v2 : seq<T>) : seq<T>
        requires isCompleteTree(r)                              
        requires 1 <= |p| <= height(r) - 1      
        requires exists i :: 0 <= i < |p| && p[i] == 0
        requires |v1| == |v2| == |p|
        requires forall i :: 0 <= i < |p| ==>
            v1[i] == nodeAt(p[.. i + 1],r).v 
        requires forall i :: 0 <= i < |p| ==>
            p[i] == 1 ==> v2[i] == siblingAt(p[.. i + 1],r).v 

        ensures |computeLeftSiblingOnNextPath(p, r, v1, v2)| == |v1|
    {
        if |p| == 1 then
            assert(p[0] == 0);
                v1
        else 
            assert(|p| >= 2);
            if p[|p| - 1] == 0 then 
                //  Next path is p[..|p| - 1] + [1]
                //  nextPath(p) and p agree on first |p| - 1 steps 
                //  Collect values from v2[..|p| - 1 ] and add value at NodeAt(p,r)
                v2[..|p| - 1] + [v1[|p| - 1 ]]
            else 
                //  Nextpath is nextPath(p[.. |p| - 1]) + [0]
                //  p[|p| - 1] == 0, next path will lead to another branch from ancestor
                //  At that level in the tree nextPath(p)[|p| - 1] == 0 so whatever is good
                assert(forall i :: 0 <= i < |p| - 1 ==>
                        p[.. i + 1] == p[..|p| - 1][.. i + 1]);

                computeLeftSiblingOnNextPath(p[.. |p| - 1], r, v1[..|p| - 1], v2[..|p| - 1]) + [v1[|p| - 1 ]]
    } 

    lemma foo500<T>(p: seq<bit>, r : ITree<T>, v1 : seq<T>, v2 : seq<T>)
        requires isCompleteTree(r)                              
        requires 1 <= |p| <= height(r) - 1      

        requires exists i :: 0 <= i < |p| && p[i] == 0
        requires |v1| == |v2| == |p|
        requires forall i :: 0 <= i < |p| ==>
            v1[i] == nodeAt(p[.. i + 1],r).v 
        requires forall i :: 0 <= i < |p| ==>
            p[i] == 1 ==> v2[i] == siblingAt(p[.. i + 1],r).v 

        ensures forall i :: 0 <= i < |p| && nextPath(p)[i] == 1 ==> 
                computeLeftSiblingOnNextPath(p, r, v1, v2)[i] == siblingAt(nextPath(p)[..i + 1],r).v
    {    
        if |p| == 1 {
            forall (i : int |  0 <= i < |p| && nextPath(p)[i] == 1)
                ensures computeLeftSiblingOnNextPath(p, r, v1, v2)[i] == siblingAt(nextPath(p)[..i + 1],r).v
            {
                //  i must be zero
                assert(i == 0);
                assert(siblingAt(nextPath(p)[..i + 1],r).v == nodeAt(p[.. i + 1],r).v) ;
            }
            // assert()
        } else {
            //  |p| >= 2
            forall (i : int |  0 <= i < |p| && nextPath(p)[i] == 1)
                ensures computeLeftSiblingOnNextPath(p, r, v1, v2)[i] == siblingAt(nextPath(p)[..i + 1],r).v
            {
                if (p[|p| - 1] == 0) {
                    //  next path must end with 1 and hence p[|p| - 1] == 0
                    assert(nextPath(p) == p[..|p| - 1] + [1]);
                    assert(p[|p| - 1] == 0);
                    if ( i < |p| - 1 ) {
                        //  nextpath prefix is prefix of p
                        calc {
                            siblingAt(nextPath(p)[..i + 1],r).v ;
                            == calc {
                                nextPath(p)[..i + 1];
                                ==
                                p[.. i + 1];
                            }
                            siblingAt(p[.. i + 1], r).v ;
                            ==
                            v2[i];
                            ==
                            v2[..|p| - 1][i];
                            == 
                            (v2[..|p| - 1] + [v1[|p| - 1 ]])[i];
                            ==
                            computeLeftSiblingOnNextPath(p, r, v1, v2)[i];
                        }
                    
                    } else {
                        // i == |p| - 1
                        calc {
                            siblingAt(nextPath(p)[..i + 1],r).v ;
                            == calc == {
                                i ;
                                |p| - 1;
                            }
                            siblingAt(nextPath(p)[..|p|],r).v ;
                            == { fullSliceIsSeq(nextPath(p)) ;}
                            siblingAt(nextPath(p),r).v;
                            == { foo900(p[..|p| - 1], r, 1); }
                            nodeAt(p[..|p| - 1] + [0], r).v;
                            == calc {
                                p ;
                                ==
                                p[..|p| - 1] + [0];
                            }
                            nodeAt(p, r).v;
                            == calc {
                                p ;
                                ==
                                p[..|p| + 1 - 1];
                            }
                            nodeAt(p[.. |p| + 1 - 1],r).v;
                            ==
                            v1[|p| - 1];
                            ==
                            computeLeftSiblingOnNextPath(p, r, v1, v2)[|p| - 1] ;
                            == calc {
                                i ;
                                ==
                                |p| - 1;
                            }
                            computeLeftSiblingOnNextPath(p, r, v1, v2)[i] ;
                        }
                    }
                } else {
                    // p[|p| - 1] == 1
                    assert(nextPath(p) == nextPath(p[.. |p| - 1]) + [0]);
                    if ( i < |p| - 1 ) {
                        assert(p[|p| - 1] == 1);
                        //  Induction on p[.. |p| - 1]
                        //  Check pre conditions to apply lemma inductively
                       
                        //  Requirement on v1
                        forall (k : int | 0 <= k < |p[.. |p| - 1]| ) 
                            ensures v1[k] == // nodeAt(p[.. k + 1],r).v == 
                                          nodeAt(p[.. |p| - 1][.. k + 1],r).v
                        {
                            calc {
                                v1[k];
                                ==
                                nodeAt(p[.. k + 1],r).v ;
                                == calc {
                                    p[.. |p| - 1][..k + 1] ;
                                    ==
                                    p[..k + 1];
                                }
                                nodeAt(p[.. |p| - 1][.. k + 1],r).v ;
                            }
                        }

                        //  Requirement on v2
                        forall (k : int | 0 <= k < |p[.. |p| - 1]| && p[.. |p| - 1][k] == 1 ) 
                            ensures v2[k] == // nodeAt(p[.. k + 1],r).v == 
                                          siblingAt(p[.. |p| - 1][.. k + 1],r).v
                        {
                            calc {
                                v2[k];
                                ==
                                siblingAt(p[.. k + 1],r).v ;
                                == calc {
                                    p[.. |p| - 1][..k + 1] ;
                                    ==
                                    p[..k + 1];
                                }
                                siblingAt(p[.. |p| - 1][.. k + 1],r).v ;
                            }
                        }
                        
                        //  Induction hypothesis on p[.. |p| - 1], ... 
                        foo500(p[.. |p| - 1], r, v1[..|p| - 1] , v2[..|p| - 1]);

                        calc {
                            computeLeftSiblingOnNextPath(p[..|p| - 1], r, v1[..|p| - 1], v2[..|p| - 1])[i] ;
                            ==
                            siblingAt(nextPath(p[..|p| - 1])[..i + 1],r).v;
                            == calc {
                                nextPath(p[..|p| - 1])[..i + 1];
                                == 
                                nextPath(p)[.. i + 1];
                            }
                            siblingAt(nextPath(p)[..i + 1],r).v;
                        }
                    } else {
                        //  i == |p| - 1 and nextpath(p)[|p| - 1] == 0 so trivially true
                        //  Thanks Dafny 
                    }
                }
            }
        }
    }
}