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
include "../trees/CompleteTrees.dfy"
include "../synthattribute/GenericComputation.dfy"
include "../helpers/Helpers.dfy"
include "../MerkleTrees.dfy"
include "../paths/NextPathInCompleteTreesLemmas.dfy"
include "../paths/PathInCompleteTrees.dfy"
include "../seqofbits/SeqOfBits.dfy"
include "../helpers/SeqHelpers.dfy"
include "../trees/Trees.dfy"

module LeftSiblings {
 
    import opened DiffTree
    import opened CompleteTrees
    import opened GenericComputation
    import opened Helpers
    import opened MerkleTrees
    import opened NextPathInCompleteTreesLemmas
    import opened PathInCompleteTrees
    import opened SeqOfBits
    import opened SeqHelpers
    import opened Trees

    /**
     *  If b and b' agree on values at which p[i] == 1 and b has siblings at p[..], then 
     *  b' has siblings at same location.  
     */
    lemma {:induction p, r} siblingsLeft(p : seq<bit>, r : Tree<int>, b : seq<int>, b': seq<int>, k : nat, i : nat) 

        requires isCompleteTree(r)
        /** `r` is decorated with attribute `f`. */
        requires isDecoratedWith(diff, r)
        requires height(r) >= 2

        /**  all leaves after the k leaf are zero. */
        requires k < |leavesIn(r)|
        requires forall i :: k < i < |leavesIn(r)| ==> leavesIn(r)[i].v == 0

        /** p is the path to k leaf in r. */
        requires hasLeavesIndexedFrom(r, i)
        requires |p| == height(r) - 1
        requires nodeAt(p, r) == leavesIn(r)[k]

        requires |b| == |p|
        /** `b` contains values at left siblings on path `p`. */
        requires forall i :: 0 <= i < |b| ==> p[i] == 1 ==> b[i] == siblingAt(take(p, i + 1), r).v

        /** b and b' agree on values at indices where p[i] == 1, and otherwise b'[i] == 0 */
        requires |b'| == |b| && forall i :: 0 <= i < |b'| ==> if p[i] == 1 then b'[i] == b[i] else b'[i] == 0 

        ensures forall i :: 0 <= i < |b'| ==> b'[i] == siblingAt(take(p, i + 1), r).v
    {
        leavesRightOfNodeAtPathZeroImpliesRightSiblingsOnPathZero(r, k, p, i);   
    }

    /**
     *  Collect the left siblings of a path.
     */
    function collectSiblingsValues(p : seq<bit>, r : Tree<int>, k : nat, index : nat) : seq<int>
        requires isCompleteTree(r)
        requires hasLeavesIndexedFrom(r, index)
        requires height(r) >= 2

        /** `r` is decorated with attribute `f`. */
        requires isDecoratedWith(diff, r)
        // requires isDecoratedWith(diff, r')
        requires height(r) >= 2

        /**  all leaves after the k leaf are zero. */
        requires k < |leavesIn(r)| 

        requires 1 <= |p| == height(r) - 1
        requires nodeAt(p, r) == leavesIn(r)[k]

        ensures |collectSiblingsValues(p, r, k, index)| == |p|
        // ensures forall i :: 0 <= i < |p| ==> collectSiblingsValues(p, r, k, index)[i] == siblingAt(take(p, i + 1), r).v

    {
        if |p| == 1 then
            //  tree has a root and two leaves
            match r 
                case Node(_, lc, rc) =>
                    [if first(p) == 0 then rc.v else lc.v]
        else 
            //  collect values of sibling of current node and pre-prend
            match r 
                case Node(_, lc, rc) =>
                    //  Prove pre-conditions on lc or rc before recursive call to collectSiblingsValues.
                    childrenInCompTreesHaveHeightMinusOne(r);
                    childrenCompTreeValidIndex(r, height(r), index);
                    completeTreeNumberLemmas(r);
                    initPathDeterminesIndex(r, p, k, index);
                    simplifyNodeAtFirstBit(p, r);

                    if first(p) == 0 then 
                        [rc.v] + collectSiblingsValues(tail(p), lc, k, index)
                    else 
                        [lc.v] + collectSiblingsValues(tail(p), rc, k - power2(height(r) - 1) / 2, index + power2(height(r) - 1) / 2)
    }
   
    // lemma foo000

    lemma leftSiblingsOfPathDoesNotDependOnvalueOfLeafAtPath(p : seq<bit>, r : Tree<int>, r' : Tree<int>, a : int,  b : int, k: nat, index: nat)

        requires isCompleteTree(r)
        requires isCompleteTree(r')
        /** `r` is decorated with attribute `f`. */
        requires isDecoratedWith(diff, r)
        requires isDecoratedWith(diff, r')
        requires height(r) == height(r') >= 2

        requires hasLeavesIndexedFrom(r, index)
        requires hasLeavesIndexedFrom(r', index)

        /**  all leaves after the k leaf are zero. */
        requires k < |leavesIn(r)| == |leavesIn(r')|
        requires 1 <= |p| == height(r) - 1

        requires forall i :: 0 <= i < |leavesIn(r)| && i != k ==> leavesIn(r)[i].v == leavesIn(r')[i].v
        requires leavesIn(r)[k].v == a
        requires leavesIn(r')[k].v == b

        requires nodeAt(p, r) == leavesIn(r)[k]

        ensures nodeAt(p, r') == leavesIn(r')[k]

        // ensures leftSiblings(p, r, a, k, index) == leftSiblings(p, r', b, k, index)
    {   
        //  nodeAt(p, r') == leavesIn(r')[k]
        pathToIndexIsBinaryOfIndex(p, r, k, index);
        assert( bitListToNat(p) == k);
        leafAtPathIsIntValueOfPath(p, r', k, index);
        assert(nodeAt(p, r') == leavesIn(r')[k]);

        // if |p| == 1 {
        //     //  Thanks Dafny
        //     assume(leftSiblings(p, r, k, index) == leftSiblings(p, r', k, index));
        // } else {
        //     //  Thanks Dafny
        //     assume(leftSiblings(p, r,  k, index) == leftSiblings(p, r', k, index));
        // }
    }
    

 }