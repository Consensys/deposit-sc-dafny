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

include "CompleteTrees.dfy"
include "Helpers.dfy"
include "SeqOfBits.dfy"
include "SeqHelpers.dfy"
include "Trees2.dfy"

module PathInCompleteTrees {

    import opened CompleteTrees
    import opened Helpers
    import opened SeqOfBits
    import opened SeqHelpers
    import opened Trees 

    /**
     *  The node at the end of a path.
     *
     *  @param  p   A path (left/right) in a binary tree.
     *  @param  r   A complete binary tree.
     *
     *  @returns    The node of the tree that is the target of path `p`.
     */
    function nodeAt(p : seq<bit>, r: Tree) : Tree
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
                case Node(_, lc, rc) => 
                    nodeAt(p[1..], if p[0] == 0 then lc else rc)
    }

    /**
     *  The sibling of a node at a given path.
     *  
     *  @param  p   A path (left/right)..
     *  @param  r   A complete binary tree.
     *
     *  @returns    The node of the tree that is the target of path `p`.
     */
    function siblingAt(p : seq<bit>, r :Tree) : Tree
        requires 1 <= |p| < height(r) 
        requires isCompleteTree(r)
    {
        if p[|p| - 1] == 0 then
            nodeAt(p[..|p| - 1] + [1], r)
        else
            nodeAt(p[..|p| - 1] + [0], r)
    }      

    /**
     *  For path of length >= 2, siblingAt can be computed 
     *  recursively by choosing which child (left or right) p starts with.
     *   
     */
    lemma simplifySiblingAtFirstBit(p : seq<bit>, r :Tree)
        requires 2 <= |p| < height(r) 
        requires isCompleteTree(r)
        ensures match r 
            case Node(_, lc, rc) =>
                siblingAt(p, r) == 
                siblingAt(p[1..], if p[0] == 0 then lc else rc)
    {
        match r 
            case Node(_, lc, rc) =>
            
                var oppLastP := 1 - p[|p| - 1];
                var p1 := p[..|p| - 1];
                //  build path to sibling by flipping last value of p
                var b := p[..|p| - 1] + [oppLastP];                
                calc == {
                    siblingAt(p, r);
                    nodeAt(b, r);
                    nodeAt(b[1..], if b[0] == 0 then lc else rc);
                    calc == {  //  b[0] is same as p[0]
                        b[0];
                        p[0];
                    }
                    nodeAt(b[1..], if p[0] == 0 then lc else rc);
                    calc == {  //  b[1..] can be rewritten using p
                        b[1..];
                        p[1..][..|p[1..]| - 1] + [oppLastP];
                    }
                    nodeAt(p[1..][..|p[1..]| - 1] + [oppLastP], if p[0] == 0 then lc else rc);
            }
    }
    
    /**
     *  In a complete tree, the height if a node after a path is
     *  the height of the tree minus length of the path.
     *  
     *  @note   Does not seem to be used any more.
     */
    lemma heightOfNodeAt(p : seq<bit>, r : Tree) 
        requires 1 <= |p| < height(r) 
        requires isCompleteTree(r)
        
        ensures height(nodeAt(p, r)) == height(r) - |p| 
    { }

    /**
     *  The node after a path is a complete tree and can be computed
     *  using initial prefix and last bit.
     */
    lemma nodeAtisCompleteAndHeight(p : seq<bit>, r : Tree, a : bit) 
        requires 1 <= |p| < height(r) - 1
        requires isCompleteTree(r)
        
        ensures height(nodeAt(p, r)) == height(r) - |p| 
            && isCompleteTree(nodeAt(p, r))
            && nodeAt(p + [a], r) == nodeAt([a], nodeAt(p, r))
    { 
        if |p| == 1 {
            //  Thanks Dafny
        } else {
            //  First part ensured by the following lemma:
            heightOfNodeAt(p, r) ;
            //  Second part 
            match r 
                case Node(_, lc, rc) => 
                    calc == {
                        nodeAt(p + [a], r);
                        ==
                        nodeAt((p + [a])[1..], if p[0] == 0 then lc else rc);
                        == calc {
                            (p + [a])[1..] ;
                            ==
                            p[1..] + [a];
                        }
                        nodeAt(p[1..] + [a], if p[0] == 0 then lc else rc);
                    }
        }
    }

    /**
     *  Initial path determines index range.
     */
    lemma initPathDeterminesIndex(r : Tree, p : seq<bit>, k : nat, i : nat) 
        requires isCompleteTree(r)
        /** Path to a leaf. */
        requires 1 <= |p| == height(r) - 1
        requires k < power2(height(r) - 1) == |leavesIn(r)|
        /** p is a path to the k-th leaf. */
        requires hasLeavesIndexedFrom(r, i)

        requires nodeAt(p,r) == leavesIn(r)[k]

        ensures match r 
            case Node(_, lc, rc) =>
                (p[0] == 0 && k < power2(height(r) - 1)/2)
                ||
                (p[0] == 1 && k >= power2(height(r) - 1)/2)
    {
        childrenInCompTreesHaveHalfNumberOfLeaves(r, height(r));
    }

    /**
     *  A path to the k-th leaf is the binary encoding of k.
     */
    lemma pathToIndexIsBinaryOfIndex(p : seq<bit>, r :  Tree, k : nat, i : nat) 
        requires isCompleteTree(r)
        requires 1 <= |p| == height(r) - 1 
        requires k < |leavesIn(r)|
        requires hasLeavesIndexedFrom(r, i)
        requires nodeAt(p, r) == leavesIn(r)[k]
        ensures bitListToNat(p) == k
        decreases p 
    {
        if |p| == 1 {
            initPathDeterminesIndex(r, p, k, i);
            if p[0] == 0 {
                assert(bitListToNat(p) == 0 == k);
            } else {
                assert(bitListToNat(p) == 1 == k);
            }
        } else {
            //  r is not a leaf
            match r 
                case Node(_, lc, rc) => 
                    if p[0] == 0 {
                        //  left lc
                        assert(nodeAt(p, r) == nodeAt(p[1..], lc));
                        //  HI on rc
                        childrenInCompTreesHaveSameNumberOfLeaves(r);
                        initPathDeterminesIndex(r, p, k, i);
                        assert( k < power2(height(r) - 1)/ 2);
                        assert(|leavesIn(lc)| == power2(height(r) - 1)/ 2);

                        childrenCompTreeValidIndex(r, height(r), i);

                        pathToIndexIsBinaryOfIndex(p[1..], lc, k, i);
                    } else {
                        //  p[0] == 1
                        assert(nodeAt(p, r) == nodeAt(p[1..], rc));
                        childrenInCompTreesHaveSameNumberOfLeaves(r);
                        assert(nodeAt(p, r) == nodeAt(p, r));

                        initPathDeterminesIndex(r, p, k, i);
                        assert( k >= power2(height(r) - 1)/ 2);
                        assert(|leavesIn(rc)| == power2(height(r) - 1)/ 2);
                        // assert(|leavesIn(rc)| == power2(height(r) - 1)/ 2);

                        childrenCompTreeValidIndex(r, height(r), i);
                        //  induction on 
                        var k' := k - power2(height(r) - 1)/ 2 ;
                        assert(leavesIn(r)[k] == leavesIn(rc)[k']);
                        pathToIndexIsBinaryOfIndex(p[1..], rc, k',  i + power2(height(r) - 1) / 2);

                    }
        }
    }

    /**
     *  Leaf at path is indexed by intvalue of path.
     */
    lemma leafAtPathIsIntValueOfPath(p : seq<bit>, r :  Tree, k : nat, i : nat) 
        requires isCompleteTree(r)
        requires hasLeavesIndexedFrom(r, i)
        requires 1 <= |p| == height(r) - 1 
        requires k < |leavesIn(r)|
        requires bitListToNat(p) == k
        ensures nodeAt(p, r) == leavesIn(r)[k]
        decreases p 
    {
        if |p| == 1 {
            if p[0] == 0 {
                initPathDeterminesIndex(r, p, k, i);
                assert(k == 0);
                assert(bitListToNat(p) == 0);
                assert(nodeAt(p, r) == leavesIn(r)[0]);
            } else {
                assert(p[0] == 1);
                initPathDeterminesIndex(r, p, k, i);
                assert(k == 1);
                assert(bitListToNat(p) == 1);
                assert(nodeAt(p, r) == leavesIn(r)[k]);
            }
        } else {
            //  r is not a leaf
            match r 
                case Node(_, lc, rc) => 
                    childrenCompTreeValidIndex(r, height(r), i);
                    if p[0] == 0 {
                        //  left lc
                        assert(nodeAt(p, r) == nodeAt(p[1..], lc));
                        //  HI on rc
                        childrenInCompTreesHaveSameNumberOfLeaves(r);
                        initPathDeterminesIndex(r, p, k, i);
                        assert( k < power2(height(r) - 1)/ 2);
                        assert(|leavesIn(lc)| == power2(height(r) - 1)/ 2);
                        // foo302(p[1..], lc, k);
                    } else {
                        //  p[0] == 1
                        assert(nodeAt(p, r) == nodeAt(p[1..], rc));
                        childrenInCompTreesHaveSameNumberOfLeaves(r);

                        assert( k >= power2(height(r) - 1)/ 2);
                        assert(|leavesIn(rc)| == power2(height(r) - 1)/ 2);
                        var k' := k - power2(height(r) - 1)/ 2 ;

                        childrenInCompTreesHaveHalfNumberOfLeaves(r , height(r));
                        assert(leavesIn(rc) == leavesIn(r)[power2(height(r) - 1) / 2 ..]);
                        assert(leavesIn(rc)[k'] == leavesIn(r)[power2(height(r) - 1) / 2 ..][k']);
                        assert(nodeAt(p[1..], rc) == nodeAt(p, r));
                        // assert(nodeAt(p, r) == leavesIn(r)[k]);

                        leafAtPathIsIntValueOfPath(p[1..], rc, k', i + power2(height(r) - 1) / 2);
                        assert(nodeAt(p[1..], rc) == leavesIn(rc)[k']);
                        assert( leavesIn(rc)[k'] == leavesIn(r)[k]);
                        initPathDeterminesIndex(rc, p[1..], k', i + power2(height(r) - 1) / 2);
                        // assume( nodeAt(p, r) == leavesIn(r)[k]);
                    }
        }
    }

    /**
     *  One-to-one correspondence between path an index of leaf.
     */
    lemma indexOfLeafisIntValueOfPath(p : seq<bit>, r :  Tree, k : nat) 
        requires isCompleteTree(r)
        requires hasLeavesIndexedFrom(r, 0)
        requires 1 <= |p| == height(r) - 1 
        requires k < |leavesIn(r)|
        ensures bitListToNat(p) == k <==> nodeAt(p, r) == leavesIn(r)[k]
    {
        if (bitListToNat(p) == k) {
            leafAtPathIsIntValueOfPath(p, r, k, 0);
        } else if ( nodeAt(p, r) == leavesIn(r)[k]) {
            pathToIndexIsBinaryOfIndex(p, r, k, 0);
        }
    }

    /**
     *  A path to a leaf of index < |leavesin{r)| -1 has a zero in it.
     */
    lemma pathToLeafInInitHasZero(p: seq<bit>, r :  Tree, k : nat, i : nat)
        requires |p| == height(r) - 1
        requires isCompleteTree(r)
        requires hasLeavesIndexedFrom(r, i)
        requires k < |leavesIn(r)| - 1
        requires nodeAt(p, r) == leavesIn(r)[k]
        ensures exists i :: 0 <= i < |p| && p[i] == 0
        decreases p 
    {
        if |p| == 1 {
            //  k < |leavesIn(r)| <==> k < 1 <==> k == 0, apply initPathDeterminesIndex ==> p[0] == 0
            initPathDeterminesIndex(r, p, k, i);
        } else {
            if p[0] == 0 {
                //  p[0] is a witness
            } else {
                //  r is a node (not a leaf) and path leads to a node in rc
                match r
                    case Node(_, lc, rc) =>
                        //  Use relation on leavesIn(rc) and leavesIn(r)
                        //  leavesIn(r)[k] == leavesIn(rc)[k - power2(height(r) - 1)/2]
                        childrenInCompTreesHaveHalfNumberOfLeaves(r , height(r));

                        //  k >= power2(height(r) -1 ) /2 by
                        initPathDeterminesIndex(r, p, k, i);

                        var k' := k - power2(height(r) - 1) / 2;
                        //  induction on rc
                        pathToLeafInInitHasZero(p[1..], rc, k', i + power2(height(r) - 1)/2);
            }
        }
    }

   /**
     *  A path to a leaf which is not the rightmost one must have 
     *  a zero.
     *
     *  @todo simplify this lemma by establishing a property on bitListToNat:
     *  bitListtoNat(p) == power2(n) - 1 iff the first n bits are 1.
     */
    lemma aPathToNonLastLeafhasZero(p: seq<bit>, r :  Tree, k : nat, i : nat) 
        requires isCompleteTree(r)
        requires hasLeavesIndexedFrom(r, i)
        requires 1 <= |p| == height(r) - 1
        requires 0 <= k < |leavesIn(r)| - 1
        requires nodeAt(p, r) == leavesIn(r)[k]
        ensures  exists i :: 0 <= i < |p| && p[i] == 0 
        decreases p 
    {
        
        if |p| == 1 {
            //  Thanks Dafny
            assert(k == 0);
            initPathDeterminesIndex(r, p, k, i);
            assert(p[0] == 0);
        } else {
            if p[0] == 0 {
                //  
            } else {
                // p[0] == 1, apply to rc
                match r
                    case Node(_, _, rc)=>
                        assert(isCompleteTree(rc));
                        assert(1 <= |p[1..]|);
                        assert(nodeAt(p, r) == nodeAt(p[1..], rc));
                        // assert(|leavesIn(rc)| == )
                        childrenInCompTreesHaveHalfNumberOfLeaves(r, height(r));
                        assert(p[0] == 1);
                        initPathDeterminesIndex(r, p, k, i);
                        assert( 0 <= k - power2(height(r) - 1) / 2);
                        assert( k - power2(height(r) - 1)/ 2 < |leavesIn(rc)| - 1);
                        // assert(nodeAt(p[1..],rc) == );
                        aPathToNonLastLeafhasZero(p[1..], rc, k - power2(height(r) - 1)/2, i + power2(height(r) - 1) / 2);
                        assert(exists i ::  0 <= i < |p[1..]| && p[1..][i] == 0); 
                        // var i :|  0 <= i < |p[1..]| && p[1..][i] == 0 ;
            }
        }
    } 

    /**
     *  Next path from a leaf must go to the next leaf
     */
    lemma nextPathNextLeaf(p: seq<bit>, r :  Tree, k : nat) 
        requires isCompleteTree(r)                              // 1.
        requires hasLeavesIndexedFrom(r, 0)
        requires 1 <= |p| == height(r) - 1                      // 2.
        requires 0 <= k < |leavesIn(r)| - 1                     // 3.
        requires nodeAt(p, r) == leavesIn(r)[k]                 // 4.
        ensures exists i ::  0 <= i < |p| && p[i] == 0          //  P1
        ensures  nodeAt(nextPath(p), r) == leavesIn(r)[k + 1]   //  P2
    {
        //  proof of P1
        aPathToNonLastLeafhasZero(p, r, k, 0);
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
    lemma {:induction p, r, k} leftSiblingAtNextPathOnPathOrSiblingOfPath(p: seq<bit>, r :  Tree, k : nat)
        requires isCompleteTree(r)      
        requires hasLeavesIndexedFrom(r, 0)                        
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
       aPathToNonLastLeafhasZero(p, r , k, 0) ;
       foo32(p, r);
    }

    /**
     *  Left siblings of nextPath are on path or are sibling of path.
     */
    lemma foo32(p: seq<bit>, r :  Tree)
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
                    assert(p[|p| - 1] == 1);
                    assert(exists i ::  0 <= i < |p| - 1  && p[i] == 0 );
                    // assert(p[.. |p| - 1] == )
                    assert(exists i {:trigger p[.. |p| - 1][i]} ::  0 <= i < |p[.. |p| - 1]|   && p[.. |p| - 1][i] == 0 );

                    if ( i < |p| - 1) {
                        //  induction on p[..|p| - 1]
                        foo32(p[.. |p| - 1], r);

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
     *  @param  r   The root of the tree.
     *  @param  v1  The values of the nodes on the path.
     *  @param  v2  The values of the nodes that are left siblings of nodes on the path.
     *  @returns    The values of the nodes that are left siblings of nextPath(p).
     */
    function method computeLeftSiblingOnNextPath<T>(p: seq<bit>, r :  Tree<T>, v1 : seq<T>, v2 : seq<T>) : seq<T>
        requires isCompleteTree(r)                              
        requires 1 <= |p| <= height(r) - 1      
        requires exists i :: 0 <= i < |p| && p[i] == 0
        requires |v1| == |v2| == |p|
        requires forall i :: 0 <= i < |p| ==>
            v1[i] == nodeAt(p[.. i + 1],r).v 
        requires forall i :: 0 <= i < |p| ==>
            p[i] == 1 ==> v2[i] == siblingAt(p[.. i + 1],r).v 

        ensures |computeLeftSiblingOnNextPath(p, r, v1, v2)| == |v1|

        decreases p
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
                assert(forall i {:trigger p[.. i + 1]} :: 0 <= i < |p| - 1 ==>
                        p[.. i + 1] == p[..|p| - 1][.. i + 1]);

                computeLeftSiblingOnNextPath(p[.. |p| - 1], r, v1[..|p| - 1], v2[..|p| - 1]) + [v1[|p| - 1 ]]
    } 

    /**
     *  computeLeftSiblingOnNextPath returns values on left siblings of next path.
     */
    lemma computeOnNextPathCollectsValuesOfNextLeftSiblings<T>(p: seq<bit>, r :  Tree<T>, v1 : seq<T>, v2 : seq<T>)
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
                assert(p[0] == 0);
                assert(nextPath(p)[i] == 1);
                calc {
                    computeLeftSiblingOnNextPath(p, r, v1, v2)[i];
                    computeLeftSiblingOnNextPath(p, r, v1, v2)[0];
                    v1[0];
                }
                calc == {
                    siblingAt(nextPath(p)[..i + 1],r).v ;
                    siblingAt(nextPath(p)[..1],r).v;
                    siblingAt(nextPath(p),r).v;
                    siblingAt([1],r).v;
                    nodeAt([1][..0] + [0],r).v;
                    nodeAt(p[..1],r).v;
                    v1[0];
                }
                // assert(siblingAt(nextPath(p)[..i + 1],r).v == nodeAt(p[.. i + 1],r).v) ;
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
                            == 
                            // { fullSliceIsSeq(nextPath(p)) ;}
                            calc == {
                                nextPath(p)[..|p|];
                                nextPath(p);
                            }
                            siblingAt(nextPath(p),r).v;
                            == // { foo900(p[..|p| - 1], r, 1); }
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
                        computeOnNextPathCollectsValuesOfNextLeftSiblings(p[.. |p| - 1], r, v1[..|p| - 1] , v2[..|p| - 1]);

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