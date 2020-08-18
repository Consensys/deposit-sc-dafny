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

include "IncAlgoV1.dfy"
include "CompleteTrees.dfy"
include "ComputeRootPath.dfy"
include "GenericComputation.dfy"
include "Helpers.dfy"
include "MerkleTrees.dfy"
include "NextPathInCompleteTreesLemmas.dfy"
include "PathInCompleteTrees.dfy"
include "SeqOfBits.dfy"
include "Trees2.dfy"

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
        (r, [seed]) 
    else 
        if p[|p| - 1] == 0 then
            var r := computeRootPathDiffAndLeftSiblingsUpv2(
                        p[.. |p| - 1], 
                        valOnLeftAt[..|valOnLeftAt| - 1],   
                        diff(seed, 0) );
                        //  could use  p[.. |p| - 1] instead of valOnPAt[..|p| - 1]
                    (r.0, valOnLeftAt[.. |valOnLeftAt| - 1] + [seed])
        else      
            var r :=  computeRootPathDiffAndLeftSiblingsUpv2(
                    p[.. |p| - 1], 
                    valOnLeftAt[..|valOnLeftAt| - 1],  
                    diff(valOnLeftAt[|valOnLeftAt| - 1], seed));
                    (r.0, r.1 + [seed])
                    //  could use 0 instead of v1[|p| - 1] but need to adjust 
                    //  computeLeftSiblingOnNextPath to match that
    }

    /**
     *  Proof that version 2 is correct i.e computes correct value on root and
     *  collect values of left siblings of next path.
     */
    lemma {:induction p, b, seed} computeRootAndSiblingsv2IsCorrect(p : seq<bit>, b : seq<int>, seed: int) 
        requires |p| == |b| 
        requires |p| >= 1
        /** We prove the following property: */
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
    lemma computeRootPathDiffAndLeftSiblingsUpv2InATree(p: seq<bit>, r :  Tree<int>, v2 : seq<int>, seed : int, k : nat)

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
            (p[i] == 1 && v2[i] == siblingAt(p[.. i + 1],r).v)
            || 
            (p[i] == 0 && v2[i] == 0)

        ensures computeRootPathDiffAndLeftSiblingsUpv2(p, v2, seed).0 == r.v
        ensures computeRootPathDiffAndLeftSiblingsUpv2(p, v2, seed).1 == 
                                             computeLeftSiblingOnNextPath(p, computeAllPathDiffUp(p, v2, seed), v2)
    {
        var v1 := computeAllPathDiffUp(p, v2, seed);
        //  Fisrt, establish pre-condition that computeAllPathDiffUp(p, v2, seed) == v1
        //  is the same as the values of the nodes in the tree.
        assume(
           forall i :: 0 <= i < |p| ==>
            v1[i] == nodeAt(p[.. i + 1],r).v 
        );
       
        //  Proof that .0 is r.v
        calc {
            computeRootPathDiffAndLeftSiblingsUpv2(p, v2, seed).0;
            { v1Equalsv2subLemma(p, v2, seed, v1); }
            computeRootPathDiffAndLeftSiblingsUp(p, v2, seed, v1).0;
            { computeRootPathDiffAndLeftSiblingsUpInATree(p, r, v1, v2, seed, k); }
            r.v;
        }
    
        //  Proof of .1 is computeLeftSiblingOnNextPath(p, v1, v2)
        computeAllDiffUpPrefixes(p, v2, seed);
        calc {
            computeRootPathDiffAndLeftSiblingsUpv2(p, v2, seed).1;
            { v1Equalsv2(p, v2, seed, v1); }
            computeRootPathDiffAndLeftSiblingsUp(p, v2, seed, v1).1;
            { computeRootPathDiffAndLeftSiblingsUpInATree(p, r, v1, v2, seed, k); }
            computeLeftSiblingOnNextPath(p, v1, v2);
        }
    }

    /** 
     *  The values of the nodes on path p can be computed on-the-fly using V2 of the
     *  algorithm (that does not need a pre-computation of the values of the nodes
     *  on the path.)
     */
    lemma v1Equalsv2(p : seq<bit>, valOnLeftAt : seq<int>, seed: int, valOnPAt: seq<int>)
        requires |p| == |valOnLeftAt| ==  |valOnPAt|
        requires |p| >= 1
        requires forall i :: 0 <= i < |valOnPAt| ==> valOnPAt[i] == computeRootPathDiffUp(p[i + 1..], valOnLeftAt[i + 1..], seed) 

        ensures computeRootPathDiffAndLeftSiblingsUpv2(p, valOnLeftAt, seed).1 ==
            computeRootPathDiffAndLeftSiblingsUp(p, valOnLeftAt, seed, valOnPAt).1
    {
        if |p| == 1 {
            //  Thanks Dafny.
        } else {
            if p[|p| - 1] == 0 {
                var a := computeRootPathDiffAndLeftSiblingsUpv2(p, valOnLeftAt, seed);
                var b := computeRootPathDiffAndLeftSiblingsUp(p, valOnLeftAt, seed, valOnPAt);

                calc == {
                    a.1;
                    valOnLeftAt[.. |valOnLeftAt| - 1] + [seed];
                    calc == {
                        valOnPAt[|p| - 1];
                        computeRootPathDiffUp(p[|p| + 1 - 1..], valOnLeftAt[|p| + 1 - 1..], seed);
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
                    p[.. |p| - 1], 
                    valOnLeftAt[..|valOnLeftAt| - 1],  
                    diff(valOnLeftAt[|valOnLeftAt| - 1], seed));
                //  def of computeRootPathDiffAndLeftSiblingsUp for p[|p| - 1] == 1
                var b1 := computeRootPathDiffAndLeftSiblingsUp(
                    p[.. |p| - 1], valOnLeftAt[..|valOnLeftAt| - 1], diff(valOnLeftAt[|valOnLeftAt| - 1], seed), valOnPAt[..|p| - 1]);
                calc == {
                    computeRootPathDiffAndLeftSiblingsUpv2(p, valOnLeftAt, seed).1;
                    a1.1 + [seed];
                }
                calc == {
                    computeRootPathDiffAndLeftSiblingsUp(p, valOnLeftAt, seed, valOnPAt).1;
                    b1.1 + [valOnPAt[|p| - 1]];
                }
                calc == {
                    valOnPAt[|p| - 1];
                    computeRootPathDiffUp(p[|p| + 1 - 1..], valOnLeftAt[|p| + 1 - 1..], seed);
                    computeRootPathDiffUp([], [], seed);
                    seed;
                }
                //  Establish pre-condition for use of inductive hypothesis on p[.. |p| - 1]
                prefixOfComputation(p, valOnLeftAt, seed, valOnPAt);
                calc == {
                    a1.1;
                    { v1Equalsv2(p[.. |p| - 1], valOnLeftAt[..|valOnLeftAt| - 1], diff(valOnLeftAt[|valOnLeftAt| - 1], seed), valOnPAt[..|p| - 1]); } 
                    b1.1;
                }
            }
        }
    }

    /**
     *  Second part.
     *  @todo   Merge into v1Equalsv2.
     */
     lemma v1Equalsv2subLemma(p : seq<bit>, valOnLeftAt : seq<int>, seed: int, valOnPAt: seq<int>)
        requires |p| == |valOnLeftAt| ==  |valOnPAt|
        requires |p| >= 1
        ensures computeRootPathDiffAndLeftSiblingsUp(p, valOnLeftAt, seed, valOnPAt).0 ==
            computeRootPathDiffAndLeftSiblingsUpv2(p, valOnLeftAt, seed).0
    {   //  Thanks Dafny.
    }

 }