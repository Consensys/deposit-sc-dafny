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
    lemma {:induction r} simplifySiblingAtFirstBit(p : seq<bit>, r :Tree)
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
    lemma {:induction p, r} heightOfNodeAt(p : seq<bit>, r : Tree) 
        requires 1 <= |p| < height(r) 
        requires isCompleteTree(r)
        
        ensures height(nodeAt(p, r)) == height(r) - |p| 
    { }

    /**
     *  The node after a path is a complete tree and can be computed
     *  using initial prefix and last bit.
     */
    lemma {:induction p, r} nodeAtisCompleteAndHeight(p : seq<bit>, r : Tree, a : bit) 
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
                        nodeAt((p + [a])[1..], if p[0] == 0 then lc else rc);
                        calc == {
                            (p + [a])[1..] ;
                            p[1..] + [a];
                        }
                        nodeAt(p[1..] + [a], if p[0] == 0 then lc else rc);
                    }
        }
    }

    /**
     *  Initial path determines index range.
     */
    lemma {:induction r, p} initPathDeterminesIndex(r : Tree, p : seq<bit>, k : nat, i : nat) 
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
    lemma {:induction p, r} pathToIndexIsBinaryOfIndex(p : seq<bit>, r :  Tree, k : nat, i : nat) 
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
    lemma {:induction p, r} leafAtPathIsIntValueOfPath(p : seq<bit>, r :  Tree, k : nat, i : nat) 
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
    lemma {:induction p, r} indexOfLeafisIntValueOfPath(p : seq<bit>, r :  Tree, k : nat) 
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
    lemma {:induction p, r} pathToLeafInInitHasZero(p: seq<bit>, r :  Tree, k : nat)
        requires |p| == height(r) - 1
        requires isCompleteTree(r)
        requires hasLeavesIndexedFrom(r, 0)
        requires k < |leavesIn(r)| - 1
        requires nodeAt(p, r) == leavesIn(r)[k]
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
                power2(height(r) - 1) - 1;
                power2(|p|) - 1;
            }
            //  k < power2(|p|) - 1 && k == power2(|p|) - 1 implies false
            assert(k < power2(|p|) - 1 && k == power2(|p|) - 1);
        }
    }
}