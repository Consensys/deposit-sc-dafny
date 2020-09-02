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
 
include "DiffTree.dfy"

include "IncAlgoV1.dfy"
include "../trees/CompleteTrees.dfy"
include "../synthattribute/ComputeRootPath.dfy"
include "../synthattribute/GenericComputation.dfy"
include "../helpers/Helpers.dfy"
include "../synthattribute/LeftSiblings.dfy"
include "../MerkleTrees.dfy"
include "../paths/NextPathInCompleteTreesLemmas.dfy"
include "../paths/PathInCompleteTrees.dfy"
include "../seqofbits/SeqOfBits.dfy"
include "../helpers/SeqHelpers.dfy"
include "../trees/Trees.dfy"

module IncAlgoV2 {
 
    import opened DiffTree
    import opened IncAlgoV1
    import opened CompleteTrees
    import opened ComputeRootPath
    import opened GenericComputation
    import opened Helpers
    import opened MerkleTrees
    import opened NextPathInCompleteTreesLemmas
    import opened PathInCompleteTrees
    import opened SeqOfBits
    import opened SeqHelpers
    import opened Trees


    /**
     *  Compute the root value and the left siblings concurrently.
     *  The fact that this version and the non-optimised (V1)
     *  computeRootPathDiffAndLeftSiblingsUp computes the same result is
     *  provided by lemma v1Equalsv2.
     */
    function computeRootPathDiffAndLeftSiblingsUpv2(
        p : seq<bit>, valOnLeftAt : seq<int>, seed: int) : (int, seq<int>)
        requires |p| == |valOnLeftAt| 
        requires |p| >= 1
       
        decreases p
    {
     if |p| == 1 then
        var r := computeRootPathDiff(p, valOnLeftAt, seed);
        (r, if first(p) == 0 then [seed] else valOnLeftAt) 
    else 
        if last(p) == 0 then
            //  Optimise and compute root path only as left sibling unchanged upwards.
            (
                computeRootPathDiffUp( init(p), init(valOnLeftAt), diff(seed, 0)), 
                init(valOnLeftAt) + [seed]
            )
        else      
            var r :=  computeRootPathDiffAndLeftSiblingsUpv2(
                    init(p), 
                    init(valOnLeftAt),  
                    diff(last(valOnLeftAt), seed));
            (r.0, r.1 + [last(valOnLeftAt)])
    }

    /**
     *  Proof that version 2 is correct i.e computes correct value on root and
     *  collect values of left siblings of next path.
     */
    lemma {:induction p, b, seed} computeRootAndSiblingsv2IsCorrect(p : seq<bit>, b : seq<int>, seed: int) 
        requires |p| == |b| 
        requires |p| >= 1
        /** We prove the following property first: */
        ensures computeRootPathDiffAndLeftSiblingsUpv2(p, b, seed).0 == computeRootPathDiffUp(p, b, seed) 
        /** And with the post condition of computeRootPathDiffAndLeftSiblingsUpv2
         *  it gives the following general result: if the returned value is (r, xs)
         *  1. then r is the same as computeRootPathDiffUp
         *  2. xs is the the same as the computeLeftSiblingOnNextPath(p)
         */
        ensures  computeRootPathDiffAndLeftSiblingsUpv2(p, b, seed) == 
            (computeRootPathDiffUp(p, b, seed),
            computeLeftSiblingOnNextPath(p, computeAllPathDiffUp(p, b, seed), b)
            )
        decreases p
    {
        //  pre-compute the values on each node of the path.
        var nodeAt := computeAllPathDiffUp(p, b, seed);

        //  use computeRootPathDiffAndLeftSiblingsUp is correct 
        computeRootAndSiblingsIsCorrect(p, b, seed, nodeAt);

        //  Use v1equalsv2
        //  possible because nodeAt satisfies pre-condition
        computeAllDiffUpPrefixes(p, b, seed);
        v1Equalsv2(p, b, seed, nodeAt);
    }

    /**
     *  Proof that computeRootPathDiffAndLeftSiblingsUpv2 is correct in a tree.
     */
    lemma {:induction p, r, v2, seed} computeRootPathDiffAndLeftSiblingsUpv2InATree(p: seq<bit>, r :  Tree<int>, v2 : seq<int>, seed : int, k : nat)

        requires isCompleteTree(r)       
        /** `r` is decorated with attribute `f`. */
        requires isDecoratedWith(diff, r)

        requires k < |leavesIn(r)|
        requires forall i :: k < i < |leavesIn(r)| ==> leavesIn(r)[i].v == 0

        /** Path to k-th leaf. */
        requires hasLeavesIndexedFrom(r, 0)
        requires 1 <= |p| == height(r) - 1      
        requires nodeAt(p, r) == leavesIn(r)[k]
        requires seed == nodeAt(p,r).v 

        /** Path is not to the last leaf. */
        requires exists i :: 0 <= i < |p| && p[i] == 0
        requires |v2| == |p|

        requires forall i :: 0 <= i < |p| ==>
            (p[i] == 1 && v2[i] == siblingAt(take(p, i + 1),r).v)
            || 
            (p[i] == 0 && v2[i] == 0)

        ensures computeRootPathDiffAndLeftSiblingsUpv2(p, v2, seed).0 == r.v
        ensures computeRootPathDiffAndLeftSiblingsUpv2(p, v2, seed).1 == 
                                             computeLeftSiblingOnNextPath(p, computeAllPathDiffUp(p, v2, seed), v2)

        ensures forall i :: 0 <= i < |p| && nextPath(p)[i] == 1 ==> 
                computeRootPathDiffAndLeftSiblingsUpv2(p, v2, seed).1[i] 
                                        == siblingAt(take(nextPath(p), i + 1),r).v
    {
        var v1 := computeAllPathDiffUp(p, v2, seed);
        //  Fisrt, establish pre-condition that computeAllPathDiffUp(p, v2, seed) == v1
        //  is the same as the values of the nodes in the tree.
        computeAllPathDiffUpInATree(p, r, v2, k, seed, 0);

        //  Proof that .0 is r.v
        calc == {
            computeRootPathDiffAndLeftSiblingsUpv2(p, v2, seed).0;
            { v1Equalsv2subLemma(p, v2, seed, v1); }
            computeRootPathDiffAndLeftSiblingsUp(p, v2, seed, v1).0;
            { computeRootPathDiffAndLeftSiblingsUpInATree(p, r, v1, v2, seed, k); }
            r.v;
        }
    
        //  Proof of .1 is computeLeftSiblingOnNextPath(p, v1, v2)
        computeAllDiffUpPrefixes(p, v2, seed);
        calc == {
            computeRootPathDiffAndLeftSiblingsUpv2(p, v2, seed).1;
            { v1Equalsv2(p, v2, seed, v1); }
            computeRootPathDiffAndLeftSiblingsUp(p, v2, seed, v1).1;
            { computeRootPathDiffAndLeftSiblingsUpInATree(p, r, v1, v2, seed, k); }
            computeLeftSiblingOnNextPath(p, v1, v2);
        }

        computeLeftSiblingOnNextPathIsCorrect(p, r, v1, v2);
    }

    /** 
     *  The values of the nodes on path p can be computed on-the-fly using V2 of the
     *  algorithm (that does not need a pre-computation of the values of the nodes
     *  on the path.)
     */
    lemma {:induction p} v1Equalsv2(p : seq<bit>, valOnLeftAt : seq<int>, seed: int, valOnPAt: seq<int>)
        requires |p| == |valOnLeftAt| ==  |valOnPAt|
        requires |p| >= 1
        requires forall i :: 0 <= i < |valOnPAt| ==> 
            valOnPAt[i] == computeRootPathDiffUp(drop(p, i + 1), drop(valOnLeftAt, i + 1), seed) 

        ensures computeRootPathDiffAndLeftSiblingsUpv2(p, valOnLeftAt, seed).1 ==
            computeRootPathDiffAndLeftSiblingsUpOpt(p, valOnLeftAt, seed, valOnPAt).1

        decreases p
    {
        if |p| == 1 {
            //  Thanks Dafny.
        } else {
            if last(p) == 0 {
                var a := computeRootPathDiffAndLeftSiblingsUpv2(p, valOnLeftAt, seed);
                var b := computeRootPathDiffAndLeftSiblingsUp(p, valOnLeftAt, seed, valOnPAt);

                calc == {
                    a.1;
                    init(valOnLeftAt) + [seed];
                    calc == {
                        last(valOnPAt);
                        computeRootPathDiffUp(drop(p, |p| + 1 - 1), drop(valOnLeftAt, |p| + 1 - 1), seed);
                        computeRootPathDiffUp([], [], seed);
                        seed;
                    }
                    b.1;
                }
            } else {
                //  
                var a := computeRootPathDiffAndLeftSiblingsUpv2(p, valOnLeftAt, seed);
                var b := computeRootPathDiffAndLeftSiblingsUp(p, valOnLeftAt, seed, valOnPAt);

                //  Def of computeRootPathDiffAndLeftSiblingsUpv2 for p[|p| - 1] == 1
                var a1 := computeRootPathDiffAndLeftSiblingsUpv2(
                    init(p), 
                    init(valOnLeftAt),  
                    diff(last(valOnLeftAt), seed));
                //  def of computeRootPathDiffAndLeftSiblingsUp for p[|p| - 1] == 1
                var b1 := computeRootPathDiffAndLeftSiblingsUp(
                    p[.. |p| - 1], init(valOnLeftAt), diff(last(valOnLeftAt), seed), init(valOnPAt));
                calc == {
                    computeRootPathDiffAndLeftSiblingsUpv2(p, valOnLeftAt, seed).1;
                    a1.1 + [last(valOnLeftAt)];
                }
                calc == {
                    computeRootPathDiffAndLeftSiblingsUp(p, valOnLeftAt, seed, valOnPAt).1;
                    b1.1 + [last(valOnLeftAt)];
                }
                calc == {
                    valOnPAt[|p| - 1];
                    computeRootPathDiffUp(drop(p, |p| + 1 - 1), drop(valOnLeftAt, |p| + 1 - 1), seed);
                    computeRootPathDiffUp([], [], seed);
                    seed;
                }
                //  Establish pre-condition for use of inductive hypothesis on init(p)
                prefixOfComputation(p, valOnLeftAt, seed, valOnPAt);
                calc == {
                    a1.1;
                    { v1Equalsv2(init(p), init(valOnLeftAt), diff(last(valOnLeftAt), seed), init(valOnPAt)); } 
                    b1.1;
                }
            }
        }
    }

    /**
     *  Sublemma used in v1equalsv2.
     */
    lemma v1Equalsv2subLemma(p : seq<bit>, valOnLeftAt : seq<int>, seed: int, valOnPAt: seq<int>)
        requires |p| == |valOnLeftAt| ==  |valOnPAt|
        requires |p| >= 1

        /** v2 computes same resukt as optimised, ans optimised is same as non-optimised. */
        ensures computeRootPathDiffAndLeftSiblingsUpOpt(p, valOnLeftAt, seed, valOnPAt).0 ==
            computeRootPathDiffAndLeftSiblingsUpv2(p, valOnLeftAt, seed).0
        ensures computeRootPathDiffAndLeftSiblingsUp(p, valOnLeftAt, seed, valOnPAt).0 ==
            computeRootPathDiffAndLeftSiblingsUpv2(p, valOnLeftAt, seed).0
    {   //  Thanks Dafny.
    }

 }