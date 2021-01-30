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
include "../seqofbits/SeqOfBits.dfy"
include "../helpers/SeqHelpers.dfy"
include "../trees/Trees.dfy"

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
        requires |p| <= height(r) 
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
                    nodeAt(tail(p), if first(p) == 0 then lc else rc)
    }

    /**
     *  For path of length >= 2, nodeAt can be computed 
     *  recursively by choosing which child (left or right) p starts with.
     *   
     */
    lemma {:induction r} simplifyNodeAtFirstBit(p : seq<bit>, r :Tree)
        requires 1 <= |p| <= height(r) 
        requires isCompleteTree(r)
        ensures match r 
            case Node(_, lc, rc) =>
                nodeAt(p, r) == 
                nodeAt(tail(p), if first(p) == 0 then lc else rc)
    {   //  Thanks Dafny
    }

     /**
     *  Simplify a path to a sibling at a given index.
     */
    lemma {:induction false} simplifyNodeAtIndexFirstBit(p : seq<bit>, r :Tree, i : nat)
        requires 1 <= i <= |p| <= height(r) 
        requires isCompleteTree(r)
        ensures match r 
            case Node(_, lc, rc) =>
                nodeAt(take(p, i), r) == 
                nodeAt(take(tail(p), i - 1), if first(p) == 0 then lc else rc)
    {
        match r 
        case Node(_, lc, rc) =>
            calc == {
                nodeAt(take(p, i), r);
                { simplifyNodeAtFirstBit(take(p, i), r) ; }
                nodeAt(tail(take(p, i)), if first(p) == 0 then lc else rc);
                { seqIndexLemmas(p, i); }
                nodeAt(take(tail(p), i - 1), if first(p) == 0 then lc else rc);
            }
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
        requires 1 <= |p| <= height(r) 
        requires isCompleteTree(r)
    {
        if last(p) == 0 then
            nodeAt(init(p) + [1], r)
        else
            nodeAt(init(p) + [0], r)
    }      

    function {:opaque} siblingValueAt<T>(p : seq<bit>, r : Tree<T>, i : nat) : T
        requires isCompleteTree(r)
        requires 1 <= i <= |p|
        requires |p| == height(r)
        requires bitListToNat(p) < power2(height(r))
    {
        siblingAt(take(p, i), r).v
    }

    /**
     *  For path of length >= 2, siblingAt can be computed 
     *  recursively by choosing which child (left or right) p starts with.
     *   
     */
    lemma {:induction r} simplifySiblingAtFirstBit(p : seq<bit>, r :Tree)
        requires 2 <= |p| <= height(r) 
        requires isCompleteTree(r)
        ensures match r 
            case Node(_, lc, rc) =>
                siblingAt(p, r) == 
                siblingAt(tail(p), if first(p) == 0 then lc else rc)
    {
        match r 
            case Node(_, lc, rc) =>
            
                var oppLastP := 1 - last(p);
                //  build path to sibling by flipping last value of p
                var b := init(p) + [oppLastP];   
                calc == {
                    first(b);
                    first(p);
                }           
                calc == {
                    tail(b);
                    take(tail(p), |tail(p)| - 1) + [oppLastP];
                }  
                calc == {
                    siblingAt(p, r);
                    nodeAt(b, r);
                    nodeAt(tail(b), if first(b) == 0 then lc else rc);
                    nodeAt(tail(b), if first(p) == 0 then lc else rc);
                    nodeAt(take(tail(p), |tail(p)| - 1) + [oppLastP], if first(p) == 0 then lc else rc);
                    siblingAt(tail(p), if first(p) == 0 then lc else rc);
                }
    }

    /**
     *  Simplify a path to a sibling at a given index.
     */
    lemma {:induction false} simplifySiblingAtIndexFirstBit(p : seq<bit>, r :Tree, i : nat)
        requires 2 <= i <= |p| <= height(r) 
        requires isCompleteTree(r)
        ensures match r 
            case Node(_, lc, rc) =>
                siblingAt(take(p, i), r) == 
                siblingAt(take(tail(p), i - 1), if first(p) == 0 then lc else rc)
    {
        match r 
        case Node(_, lc, rc) =>
            calc == {
                siblingAt(take(p, i), r);
                { simplifySiblingAtFirstBit(take(p, i), r) ; }
                siblingAt(tail(take(p, i)), if first(p) == 0 then lc else rc);
                { seqIndexLemmas(p, i); }
                siblingAt(take(tail(p), i - 1), if first(p) == 0 then lc else rc);
            }
    }

    /**
     *  In a complete tree, the height if a node after a path is
     *  the height of the tree minus length of the path.
     *  
     *  @note   Does not seem to be used any more.
     */
    lemma {:induction p, r} heightOfNodeAt(p : seq<bit>, r : Tree) 
        requires 1 <= |p| <= height(r) 
        requires isCompleteTree(r)
        
        ensures height(nodeAt(p, r)) == height(r) - |p| 
    { }

    /**
     *  The node after a path is a complete tree and can be computed
     *  using initial prefix and last bit.
     */
    lemma {:induction p, r} nodeAtisCompleteAndHeight(p : seq<bit>, r : Tree, a : bit) 
        requires 1 <= |p| < height(r)
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
                        nodeAt(tail(p + [a]), if first(p) == 0 then lc else rc);
                        { seqAppendLemmas(p , a); }
                        nodeAt(tail(p) + [a], if first(p) == 0 then lc else rc);
                    }
        }
    }

    /**
     *  Initial value of path determines index range.
     */
    lemma {:induction r, p} initPathDeterminesIndex(r : Tree, p : seq<bit>, k : nat, i : nat) 
        requires isCompleteTree(r)
        /** Path to a leaf. */
        requires 1 <= |p| == height(r) 
        requires k < power2(height(r)) == |leavesIn(r)|
        /** p is a path to the k-th leaf. */
        requires hasLeavesIndexedFrom(r, i)

        requires nodeAt(p,r) == leavesIn(r)[k] || bitListToNat(p) == k

        ensures match r 
            case Node(_, lc, rc) =>
                (first(p) == 0 && k < power2(height(r))/2)
                ||
                (first(p) == 1 && k >= power2(height(r))/2)
    {
        childrenInCompTreesHaveHalfNumberOfLeaves(r, height(r));
    }

    /**
     *  A path to the k-th leaf is the binary encoding of k.
     */
    lemma {:induction p, r} pathToIndexIsBinaryOfIndex(p : seq<bit>, r :  Tree, k : nat, i : nat) 
        requires isCompleteTree(r)
        requires 1 <= |p| == height(r) 
        requires k < |leavesIn(r)|
        requires hasLeavesIndexedFrom(r, i)
        requires nodeAt(p, r) == leavesIn(r)[k]
        ensures bitListToNat(p) == k
        decreases p 
    {
        completeTreeNumberLemmas(r);
        
        if |p| == 1 {
            calc == {
                bitListToNat(p);
                bitListToNat([first(p)]);
                { initPathDeterminesIndex(r, p, k, i); }
                k;
            }
        } else {
            //  r is not a leaf
            match r 
                case Node(_, lc, rc) => 
                    if first(p) == 0 {
                        //  left lc
                        calc == {
                            nodeAt(p, r);
                            //  by definition as first(p) == 0
                            nodeAt(tail(p), lc);
                        }
                        //  Check pre-conditions on lc before applying HI on lc
                        childrenInCompTreesHaveSameNumberOfLeaves(r);
                        assert(|leavesIn(lc)| == power2(height(r))/ 2);

                        initPathDeterminesIndex(r, p, k, i);
                        assert( k < power2(height(r))/ 2);

                        childrenCompTreeValidIndex(r, height(r), i);
                        assert(hasLeavesIndexedFrom(lc, i));

                        //  Now use result on tail(p) 
                        calc == {
                            bitListToNat(p);
                            bitListToNat(tail(p));
                            { pathToIndexIsBinaryOfIndex(tail(p), lc, k, i); }
                            k;
                        }
                    } else {
                        //  p[0] == 1
                        assert(first(p) == 1);
                        //  left rc
                        calc == {
                            nodeAt(p, r);
                            //  by definition as first(p) == 1
                            nodeAt(tail(p), rc);
                        }

                        //  Check pre-conditions on rc before applying HI on rc
                        childrenInCompTreesHaveSameNumberOfLeaves(r);
                        assert(|leavesIn(rc)| == power2(height(r))/ 2);

                        calc >= {
                            k;
                            { initPathDeterminesIndex(r, p, k, i); reveal_power2(); }
                            power2(height(r) - 1)/ 2;
                        }

                        childrenCompTreeValidIndex(r, height(r), i);
                        assert(hasLeavesIndexedFrom(rc, i + power2(height(r))/ 2));

                        //  induction on rc
                        var k' := k - power2(height(r))/ 2 ;
                        
                        childrenInCompTreesHaveHalfNumberOfLeaves(r , height(r));
                        assert(leavesIn(r)[k] == leavesIn(rc)[k']);

                        pathToIndexIsBinaryOfIndex(tail(p), rc, k',  i + power2(height(r)) / 2);
                        //  Now use result on tail(p) 
                        calc == {
                            bitListToNat(p);
                            power2(height(r)) / 2 + bitListToNat(tail(p));
                            { pathToIndexIsBinaryOfIndex(tail(p), rc, k',  i + power2(height(r)) / 2); }
                            power2(height(r)) / 2 + k';
                            k;
                        }
                    }
        }
    }

    /**
     *  Leaf at path is indexed by intvalue of path.
     */
    lemma {:induction p, r} leafAtPathIsIntValueOfPath(p : seq<bit>, r :  Tree, k : nat, i : nat) 
        requires isCompleteTree(r)
        requires hasLeavesIndexedFrom(r, i)
        requires 1 <= |p| == height(r) 
        requires k < |leavesIn(r)|
        requires bitListToNat(p) == k
        ensures nodeAt(p, r) == leavesIn(r)[k]
        decreases p 
    {
        if |p| == 1 {
            if first(p) == 0 {
                calc == {
                    nodeAt(p, r);
                    leavesIn(r)[0];
                }
                calc == {
                    bitListToNat(p);
                    k;
                    { initPathDeterminesIndex(r, p, k, i); }
                    0;
                }
            } else {
                calc == {
                    nodeAt(p, r);
                    leavesIn(r)[1];
                }
                calc == {
                    bitListToNat(p);
                    k;
                    { initPathDeterminesIndex(r, p, k, i); }
                    1;
                }
            }
        } else {
            //  r is not a leaf
            match r 
                case Node(_, lc, rc) => 
                    childrenCompTreeValidIndex(r, height(r), i);
                    if first(p) == 0 {
                        //  left lc
                        calc == {
                            nodeAt(p, r);
                            //  by definition as first(p) == 0
                            nodeAt(tail(p), lc);
                        }                        
                        //  Induction on lc
                        //  Check pre-conditions on lc before applying HI on lc
                        childrenInCompTreesHaveSameNumberOfLeaves(r);
                        assert(|leavesIn(lc)| == power2(height(r))/ 2);

                        initPathDeterminesIndex(r, p, k, i);
                        assert( k < power2(height(r))/ 2);

                        childrenCompTreeValidIndex(r, height(r), i);
                        assert(hasLeavesIndexedFrom(lc, i));

                        calc == {
                            nodeAt(p, r);
                            //  by definition as first(p) == 0
                            nodeAt(tail(p), lc);
                            //  Induction on lc
                            { leafAtPathIsIntValueOfPath(tail(p), lc, k, i) ; }
                            leavesIn(lc)[k];
                            leavesIn(r)[k];
                        }
                    } else {
                        //  p[0] == 1
                        //  right rc
                        calc == {
                            nodeAt(p, r);
                            //  by definition as first(p) == 1
                            nodeAt(tail(p), rc);
                        }

                        childrenInCompTreesHaveSameNumberOfLeaves(r);
                        assert(|leavesIn(rc)| == power2(height(r))/ 2);

                        childrenCompTreeValidIndex(r, height(r), i);
                        assert(hasLeavesIndexedFrom(rc, i + power2(height(r))/ 2));
                        
                        var k' := k - power2(height(r))/ 2 ;

                        calc == {
                            nodeAt(p, r);
                            nodeAt(tail(p), rc);
                            //  Induction on rc
                            { leafAtPathIsIntValueOfPath(tail(p), rc, k', i + power2(height(r)) / 2); }
                            leavesIn(rc)[k'];
                            { childrenInCompTreesHaveHalfNumberOfLeaves(r , height(r));}
                            leavesIn(r)[k];
                        }
                        initPathDeterminesIndex(r, p, k, i);
                        assert( k >= power2(height(r))/ 2);
                    }
        }
    }

    /**
     *  One-to-one correspondence between path an index of leaf.
     */
    lemma {:induction p, r} indexOfLeafisIntValueOfPath(p : seq<bit>, r :  Tree, k : nat) 
        requires isCompleteTree(r)
        requires hasLeavesIndexedFrom(r, 0)
        requires 1 <= |p| == height(r) 
        requires k < |leavesIn(r)|
        ensures bitListToNat(p) == k <==> nodeAt(p, r) == leavesIn(r)[k]
    {
        if (bitListToNat(p) == k) {
            leafAtPathIsIntValueOfPath(p, r, k, 0);
        } 
        if ( nodeAt(p, r) == leavesIn(r)[k]) {
            pathToIndexIsBinaryOfIndex(p, r, k, 0);
        }
    }

    /**
     *  Same as above but with parametric index instead of zero.
     */
    lemma {:induction false} indexOfLeafisIntValueOfPath2(p : seq<bit>, r :  Tree, k : nat, index: nat) 
        requires isCompleteTree(r)
        requires hasLeavesIndexedFrom(r, index)
        requires 1 <= |p| == height(r) 
        requires k < |leavesIn(r)|
        ensures bitListToNat(p) == k <==> nodeAt(p, r) == leavesIn(r)[k]
    {
        if (bitListToNat(p) == k) {
            leafAtPathIsIntValueOfPath(p, r, k, index);
        } 
        if ( nodeAt(p, r) == leavesIn(r)[k]) {
            pathToIndexIsBinaryOfIndex(p, r, k, index);
        }
    }

    /**
     *  A path to a leaf of index < |leavesin{r)| -1 has a zero in it.
     */
    lemma {:induction false} pathToLeafInInitHasZero(p: seq<bit>, r :  Tree, k : nat)
        requires |p| == height(r) 
        requires isCompleteTree(r)
        requires hasLeavesIndexedFrom(r, 0)
        requires k < |leavesIn(r)| - 1
        requires nodeAt(p, r) == leavesIn(r)[k] || bitListToNat(p) == k
        ensures exists i :: 0 <= i < |p| && p[i] == 0
        decreases p 
    {
        //  The int represented by p is k
        indexOfLeafisIntValueOfPath(p, r, k);
        assert(bitListToNat(p) == k);

        //  Proof by contradiction: assume ensures is not true, show false
        if ( !exists i :: 0 <= i < |p| && p[i] == 0 ) {
            //  p is uniformly 1's
            assert(forall i :: 0 <= i < |p| ==> p[i] == 1);
            
            //  Apply lemma on seq<bit> made of 1s
            SeqOfBits.valueOfSeqOfOnes(p);
            assert(k == power2(|p|) - 1);

            //  Apply lemma on number of leaves in a tree
            CompleteTrees.completeTreeNumberLemmas(r);
            calc == {
                k;
                <
                |leavesIn(r)| - 1;
                power2(height(r)) - 1;
                power2(|p|) - 1;
            }
            //  k < power2(|p|) - 1 && k == power2(|p|) - 1 implies false
            assert(k < power2(|p|) - 1 && k == power2(|p|) - 1);
        }
    }
}