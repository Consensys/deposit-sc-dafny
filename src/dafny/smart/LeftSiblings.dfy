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
 
include "IntTree.dfy"
include "CompleteTrees.dfy"
include "GenericComputation.dfy"
include "Helpers.dfy"
include "MerkleTrees.dfy"
include "NextPathInCompleteTreesLemmas.dfy"
include "PathInCompleteTrees.dfy"
include "SeqOfBits.dfy"
include "Trees2.dfy"

module LeftSiblings {
 
    import opened DiffTree
    import opened CompleteTrees
    import opened GenericComputation
    import opened Helpers
    import opened MerkleTrees
    import opened NextPathInCompleteTreesLemmas
    import opened PathInCompleteTrees
    import opened SeqOfBits
    import opened Trees

    /**
     *  If b and b' agree on values at which p[i] == 1 and b has siblings at p[..], then 
     *  b' has siblings at same location.  
     */
    lemma {:induction p, r} siblingsLeft(p : seq<bit>, r : Tree<int>, b : seq<int>, b': seq<int>, k : nat) 

        requires isCompleteTree(r)
        /** `r` is decorated with attribute `f`. */
        requires isDecoratedWith(diff, r)
        requires height(r) >= 2

        /**  all leaves after the k leaf are zero. */
        requires k < |leavesIn(r)|
        requires forall i :: k < i < |leavesIn(r)| ==> leavesIn(r)[i].v == 0

        /** p is the path to k leaf in r. */
        requires hasLeavesIndexedFrom(r, 0)
        requires |p| == height(r) - 1
        requires nodeAt(p, r) == leavesIn(r)[k]

        requires |b| == |p|
        /** `b` contains values at left siblings on path `p`. */
        requires forall i :: 0 <= i < |b| ==> p[i] == 1 ==> b[i] == siblingAt(p[..i + 1], r).v

        /** B abd b' agree on values at indices where p[i] == 1, and otherwise b'[i] == 0 */
        requires |b'| == |b| && forall i :: 0 <= i < |b'| ==> if p[i] == 1 then b'[i] == b[i] else b'[i] == 0 

        ensures forall i :: 0 <= i < |b'| ==> b'[i] == siblingAt(p[..i + 1], r).v
    {
        leavesRightOfNodeAtPathZeroImpliesRightSiblingsOnPathZero(r, k, p, 0);   
    }

 }