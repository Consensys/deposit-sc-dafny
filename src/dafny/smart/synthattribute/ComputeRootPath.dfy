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
include "GenericComputation.dfy"
include "../helpers/Helpers.dfy"
include "Siblings.dfy"
include "../paths/PathInCompleteTrees.dfy"
include "../seqofbits/SeqOfBits.dfy"
include "../helpers/SeqHelpers.dfy"
include "../trees/Trees.dfy"

/**
 *  Provide algorithms to compute the value of the root of a tree.
 *
 *  1. `computeRootLeftRightUp` computes the value of root bottom up using seed, left and right.
 *  2. `computeRootLeftRightUpIsCorrectForTree` shows that if left and right 
 *      are values of siblings on path of a f-decorated tree, and seed the value at the leaf, then
 *      `computeRootLeftRightUp` computes the value of the root of the tree.
 */
module ComputeRootPath {
 
    import opened CompleteTrees
    import opened GenericComputation
    import opened Helpers
    import opened Siblings
    import opened PathInCompleteTrees
    import opened SeqOfBits
    import opened SeqHelpers
    import opened Trees

    ///////////////////////////////////////////////////////////////////////////
    //  Main algorithm
    ///////////////////////////////////////////////////////////////////////////

    /**  
     *  Compute the root value on a path bottom up.
     *  
     *  @param  p       A path.
     *  @param  left    The value of `f` on each left sibling.
     *  @param  right   The value of `f` on each right sibling.
     *  @param  f       The binary operation to compute.
     *  @param  seed    The value at the end of the path.
     * 
     */
    function computeRootLeftRightUp<T>(p : seq<bit>, left : seq<T>, right: seq<T>, f : (T, T) -> T, seed: T) : T
        requires |p| == |left| == |right|
        decreases p
    {
        if |p| == 0 then
            seed 
        else 
            computeRootLeftRightUp(
                init(p), init(left), init(right), f,
                    if last(p) == 0 then f(seed, last(right)) else f(last(left), seed)
            )
    }

    ///////////////////////////////////////////////////////////////////////////
    //  Main correctness proof.
    ///////////////////////////////////////////////////////////////////////////

    /**
     *  The value computed by computeRootLeftRightUp is the same as the value of the root
     *  of the tree.
     *
     *  @param  p       A path.
     *  @param  r       A tree.
     *  @param  left    The value of `f` on siblings on path `p`.
     *  @param  right   The value of `f` on siblings on path `p`.
     *  @param  f       A binary operation.
     *  @param  seed    A value.
     */
    lemma {:induction p, r} computeRootLeftRightUpIsCorrectForTree<T>(p : seq<bit>, r : Tree<T>, left : seq<T>, right: seq<T>, f : (T,T) -> T, seed: T) 

        requires |p| == height(r) 
        requires isCompleteTree(r)
        requires isDecoratedWith(f, r)

        requires seed == nodeAt(p, r).v
        requires |right| == |left| == |p|

        /** Left and right contains siblings left and right values.  */
        requires forall i :: 0 <= i < |p| ==>
            siblingValueAt(p, r, i + 1) ==
            siblingAt(take(p, i + 1), r).v == 
                if p[i] == 0 then 
                    right[i]
                else 
                    left[i]
          
        ensures r.v == computeRootLeftRightUp(p, left, right, f, seed)

    {
        calc == {
            computeRootLeftRightUp(p, left, right, f, seed);
            { computeLeftRightUpEqualsComputeLeftRight(p, left, right, f, seed); }
            computeRootLeftRight(p, left, right, f, seed);
            { computeRootLeftRightIsCorrectForTree(p, r, left, right, f, seed); }
            r.v;
        }
    }    

    ///////////////////////////////////////////////////////////////////////////
    //  Helper functions.
    ///////////////////////////////////////////////////////////////////////////

    /**
     *  Collect all the values of attribute `f` computed on the path p using left, right and seed.
     *
     *  @param  p       A path.
     *  @param  left    The value of `f` on each left sibling.
     *  @param  right   The value of `f` on each right sibling.
     *  @param  f       The binary operation to compute.
     *  @param  seed    The value at the end of the path.
     *  @returns        The values of `f` synthesised on each node of `p`.
     *  @note           computeAll[0] is the value at the root equal to computeRootLeftRight
     */
    function computeAll<T>(p : seq<bit>, left : seq<T>, right: seq<T>, f: (T, T) -> T, seed: T) : seq<T>
        requires |p| == |left| == |right|
        ensures |computeAll(p, left, right, f, seed)| == |p| + 1
        ensures computeAll(p, left, right, f, seed)[0] == computeRootLeftRight(p, left, right, f, seed)
        decreases p
    {
        if |p| == 0 then
            [seed] 
        else 
            var r := computeAll(tail(p), tail(left), tail(right), f, seed);
            if first(p) == 0 then 
                [ f(first(r), first(right))] + r
            else 
                [ f(first(left), first(r)) ] + r
    }   

    /**
     *  Collect all the values on non-root node computed on the path p using left, right and seed.
     *
     *  @param  p       A path.
     *  @param  left    The value of `f` on each left sibling.
     *  @param  right   The value of `f` on each right sibling.
     *  @param  f       The binary operation to compute.
     *  @param  seed    The value at the end of the path.
     */
    function computeAllUp<T>(p : seq<bit>, left : seq<T>, right: seq<T>, f: (T, T) -> T, seed: T) : seq<T>
        requires |p| == |left| == |right|
        ensures |computeAllUp(p, left, right, f, seed)| == |p| 
        decreases p
    {
        if |p| == 0 then
            [] 
        else 
            computeAllUp(init(p), init(left), init(right), f,
                 if last(p) == 0 then f(seed, last(right)) else f(last(left), seed)
            ) 
            + [seed]
    }

    ///////////////////////////////////////////////////////////////////////////
    //  Helper lemmas.
    ///////////////////////////////////////////////////////////////////////////

    /**
     *  Sub-lemma to split up computation of root on left/right sibings.
     *
     *  @param  p       A path.
     *  @param  left    The value of `f` on each left sibling.
     *  @param  right   The value of `f` on each right sibling.
     *  @param  f       The binary operation to compute.
     *  @param  seed    The value at the end of the path.
     */
    lemma {:induction p, left, right} simplifyComputeAll<T>(p : seq<bit>, left : seq<T>, right: seq<T>, f : (T, T) -> T, seed: T) 
        requires 1 <= |p| == |left| == |right|
        ensures computeAll(p, left, right, f, seed) == 
            computeAll(
                init(p), init(left), init(right), f, 
                if last(p) == 0 then 
                    f(seed, last(right))
                else 
                    f(last(left), seed)
                ) + [seed]
        decreases p 
    {
        if |p| == 1 {
            //  Thanks Dafny
        } else {
            //  use the fact that init(tail(x)) == tail(init(x)) for p, left and right.
            seqLemmas(p) ;
            seqLemmas(left) ;
            seqLemmas(right) ;
            //  Dafny can work out the proof, with hint induction on tail(p), ...
            simplifyComputeAll(tail(p), tail(left), tail(right), f, seed); 
        }
    }

    /**
     *  Collect all the values of the attribute on path p (including root).
     * 
     *  @param  p       A path.
     *  @param  left    The value of `f` on each left sibling.
     *  @param  right   The value of `f` on each right sibling.
     *  @param  f       The binary operation to compute.
     *  @param  seed    The value at the end of the path.
     */
    function computeAllUp2<T>(p : seq<bit>, left : seq<T>, right: seq<T>, f: (T, T) -> T, seed: T) : seq<T>
        requires |p| == |left| == |right|
        ensures |computeAllUp2(p, left, right, f, seed)| == |p| + 1
        ensures computeAllUp2(p, left, right, f, seed)[0] == computeRootLeftRightUp(p, left, right, f, seed) == computeRootLeftRight(p, left, right, f, seed);
        decreases p
    {
        computeLeftRightUpEqualsComputeLeftRight(p, left, right, f, seed);
        if |p| == 0 then
            [seed] 
        else 
            var newSeed := if last(p) == 0 then f(seed, last(right)) else f(last(left), seed);
            computeAllUp2(init(p), init(left), init(right), f, newSeed) + [seed]
    }



    /**
     *  Relation between computeAll, computeAllUp and computeAllUp1..
     * 
     *  @param  p       A path.
     *  @param  left    The value of `f` on each left sibling.
     *  @param  right   The value of `f` on each right sibling.
     *  @param  f       The binary operation to compute.
     *  @param  seed    The value at the end of the path.
     */
    lemma {:induction p, left, right} shiftComputeAll<T>(p : seq<bit>, left : seq<T>, right: seq<T>, f: (T, T) -> T, seed: T) 
        requires |p| == |left| == |right|
        ensures computeAllUp(p, left, right, f, seed) == tail(computeAllUp2(p, left, right, f, seed))
        ensures forall i :: 0 <= i < |p| ==>  computeAllUp(p, left, right, f, seed)[i] == computeAllUp2(p, left, right, f, seed)[i + 1]
    
        decreases p 
    {
        if |p| == 0 {
            //  Thanks Dafny
        } else {
            var x := if last(p) == 0 then f(seed, last(right)) else f(last(left), seed);
            shiftComputeAll(init(p), init(left), init(right), f, x);
        }
    } 

    /**
     *  computeAll == computeAllUp2
     * 
     *  @param  p       A path.
     *  @param  left    The value of `f` on each left sibling.
     *  @param  right   The value of `f` on each right sibling.
     *  @param  f       The binary operation to compute.
     *  @param  seed    The value at the end of the path.
     */
    lemma {:induction p, left, right} computeAllUpEqualsComputeAll<T>(p : seq<bit>, left : seq<T>, right: seq<T>, f: (T, T) -> T, seed: T)
        requires |p| == |left| == |right|
        ensures computeAllUp2(p, left, right, f, seed) == computeAll(p, left, right, f, seed)

        decreases p 
    {
        if |p| == 0 {
            //  Thanks Dafny
        } else {
            if last(p) == 0 {
                calc == {
                    computeAllUp2(p, left, right, f, seed);
                    computeAllUp2(init(p), init(left), init(right), f, f(seed, last(right))) + [seed];
                    //  Induction
                    { computeAllUpEqualsComputeAll(init(p), init(left), init(right),  f, f(seed, last(right) ) )  ; }
                    computeAll(init(p), init(left), init(right),  f, f(seed, last(right))) + [seed] ;
                    { simplifyComputeAll(p, left, right, f, seed) ; }
                    computeAll(p, left, right, f, seed);
                }
            } else {
                calc == {
                    computeAllUp2(p, left, right, f, seed);
                    computeAllUp2(init(p), init(left), init(right), f, f(last(left), seed)) + [seed];
                    //  Induction
                    { computeAllUpEqualsComputeAll(init(p), init(left), init(right),  f, f(last(left), seed ) )  ; }
                    computeAll(init(p), init(left), init(right),  f, f(last(left), seed)) + [seed] ;
                    { simplifyComputeAll(p, left, right, f, seed) ; }
                    computeAll(p, left, right, f, seed);
                }
            }
        }
    }
   
    /**
     *  Computing up or down yields same result.
     *
     *  @param  p       A path.
     *  @param  left    The value of `f` on each left sibling.
     *  @param  right   The value of `f` on each right sibling.
     *  @param  f       The binary operation to compute.
     *  @param  seed    The value at the end of the path.
     */
    lemma {:induction p, left, right, f} computeLeftRightUpEqualsComputeLeftRight<T>(p : seq<bit>, left : seq<T>, right: seq<T>, f : (T, T) -> T, seed: T)
        requires |p| == |left| == |right|
        ensures computeRootLeftRightUp(p, left, right, f, seed) == computeRootLeftRight(p, left, right, f, seed)
        decreases p 
    {
        if |p| == 0 {
            //  Thanks Dafny
        } else {    
            //  |p| >= 1
            //  Split on values of last(p) 
            if last(p) == 0 {
                calc == {
                    computeRootLeftRightUp(p, left, right, f, seed);
                    computeRootLeftRightUp(init(p), init(left), init(right), f, f(seed, last(right)));
                    //  Induction assumption
                    { computeLeftRightUpEqualsComputeLeftRight(init(p), init(left), init(right), f, f(seed, last(right)));} 
                    computeRootLeftRight(init(p), init(left), init(right), f, f(seed, last(right)));
                    { simplifyComputeRootLeftRight(p, left, right, f, seed); }
                    computeRootLeftRight(p, left, right, f, seed);
                }
            } else  {
                calc == {
                    computeRootLeftRightUp(p, left, right, f, seed);
                    computeRootLeftRightUp(init(p), init(left), init(right), f, f(last(left), seed));
                    //  Induction assumption
                    { computeLeftRightUpEqualsComputeLeftRight(init(p), init(left), init(right), f, f(last(left), seed));} 
                    computeRootLeftRight(init(p), init(left), init(right), f, f(last(left), seed));
                    { simplifyComputeRootLeftRight(p, left, right, f, seed); }
                    computeRootLeftRight(p, left, right, f, seed);
                }
            }
        }
    }

    /**
     *  Sub-lemma to split up computation of root on left/right sibings.
     *  @param  p       A path.
     *  @param  left    The value of `f` on each left sibling.
     *  @param  right   The value of `f` on each right sibling.
     *  @param  f       The binary operation to compute.
     *  @param  seed    The value at the end of the path.
     */
    lemma {:induction p, left, right} simplifyComputeRootLeftRight<T>(p : seq<bit>, left : seq<T>, right: seq<T>, f : (T, T) -> T, seed: T) 
        requires 1 <= |p| == |left| == |right|
        ensures computeRootLeftRight(p, left, right, f, seed) == 
            computeRootLeftRight(
                init(p), init(left), init(right), f, 
                if last(p) == 0 then 
                    f(seed, last(right))
                else 
                    f(last(left), seed)
                )
        decreases p 
    {
        if |p| == 1 {
            // Thanks Dafny
        } else {
            //  use the fact that init(tail(x)) == tail(init(x)) for p, left and right.
            seqLemmas(p) ;
            seqLemmas(left) ;
            seqLemmas(right) ;
            //  Dafny can work out the proof, with hint induction on tail(p), ...
            simplifyComputeRootLeftRight(tail(p), tail(left), tail(right), f, seed); 
        }
    }

    /**
     *  The values computed by computeAll are the values on the nodes of the path.
     *
     *  @param  p       A path.
     *  @param  r       A tree.
     *  @param  left    The value of `f` on siblings on path `p`.
     *  @param  right   The value of `f` on siblings on path `p`.
     *  @param  f       A binary operation.
     *  @param  seed    A value.
     */
    lemma {:induction p, r, left, right} computeAllIsCorrectInATree<T>(p : seq<bit>, r : Tree<T>, left : seq<T>, right: seq<T>, f : (T, T) -> T, k : nat, seed: T, index : nat) 
        requires isCompleteTree(r)
        requires isDecoratedWith(f, r)
        requires hasLeavesIndexedFrom(r, index)

        requires k < |leavesIn(r)|
        requires |p| == height(r) 
        requires nodeAt(p, r) == leavesIn(r)[k]
        requires seed == nodeAt(p,r).v 

        requires |p| == |left| == |right|

        /** Left and right contains siblings left and right values.  */
        requires forall i :: 0 <= i < |p| ==>
            siblingAt(take(p, i + 1), r).v == 
                if p[i] == 0 then 
                    right[i]
                else 
                    left[i]

        ensures forall i :: 0 <= i <= |p| ==> 
            nodeAt(take(p, i), r).v == computeAll(p, left, right, f, seed)[i]

        decreases p 
    {
        
        forall (i : nat | 0 <= i <= |p|) 
                ensures nodeAt(take(p, i), r).v == computeAll(p, left, right, f, seed)[i]
        {
            if |p| <= 1 {
                //  Thanks Dafny
            } else {
                match r 
                    case Node(_, lc, rc) => 
                        completeTreeNumberLemmas(r);
                        assert( |leavesIn(r)| == power2(height(r)));
                        childrenCompTreeValidIndex(r, height(r), index);
                        if ( i >= 1) {
                            //  for i >= 1, induction on lc or rc depending on first(p)
                            if first(p) == 0 {
                                //  induction on lc
                                //  Prove that pre-conditions on lc are satisfied
                                childrenInCompTreesHaveSameNumberOfLeaves(r);
                                assert(|leavesIn(lc)| == power2(height(r)) / 2);
                                initPathDeterminesIndex(r, p, k, index);
                                assert(k < power2(height(r)) / 2);
                                assert(k < |leavesIn(lc)|);
                                simplifyNodeAtFirstBit(p, r);
                                assert(nodeAt(p, r) == nodeAt(tail(p), lc));
                                assert(nodeAt(tail(p), lc).v == seed);

                                projectLeftRightValuesOnChild(p, r, left, right);
                                computeAllIsCorrectInATree(tail(p), lc, tail(left), tail(right), f, k, seed, index);

                                // induction on lc
                                assert(
                                    forall k :: 0 <= k <= |tail(p)| ==> 
                                        nodeAt(take(tail(p), k), lc).v == computeAll(tail(p), tail(left), tail(right), f, seed)[k]
                                );

                                //  R1:
                                assert(nodeAt(take(tail(p), i - 1), lc).v == computeAll(tail(p), tail(left), tail(right), f, seed)[i - 1]);

                                //  
                                var x := computeAll(tail(p), tail(left), tail(right), f, seed);
                                calc == {
                                    computeAll(p, left, right, f, seed)[i];
                                    ([ f(first(x), first(right))] + x)[i];
                                    x[i - 1];
                                    nodeAt(take(tail(p), i - 1), lc).v;
                                    { simplifyNodeAtIndexFirstBit(p, r, i) ; }
                                    nodeAt(take(p, i), r).v;
                                }
                            } else {
                                //  induction on rc
                                //  Prove that pre-conditions on lc are satisfied
                                childrenInCompTreesHaveSameNumberOfLeaves(r);
                                assert(|leavesIn(rc)| == power2(height(r)) / 2);
                                initPathDeterminesIndex(r, p, k, index);
                                assert(k >= power2(height(r)) / 2);
                                var k' := k - power2(height(r)) / 2 ;
                                assert(k' < |leavesIn(rc)|);
                                simplifyNodeAtFirstBit(p, r);
                                assert(nodeAt(p, r) == nodeAt(tail(p), rc));
                                assert(nodeAt(tail(p), rc).v == seed);

                                projectLeftRightValuesOnChild(p, r, left, right);
                                computeAllIsCorrectInATree(tail(p), rc, tail(left), tail(right), f, k', seed, index + power2(height(r)) / 2);

                                // induction on lc
                                assert(
                                    forall k :: 0 <= k <= |tail(p)| ==> 
                                        nodeAt(take(tail(p), k), rc).v == computeAll(tail(p), tail(left), tail(right), f, seed)[k]
                                );

                                //  R1:
                                assert(nodeAt(take(tail(p), i - 1), rc).v == computeAll(tail(p), tail(left), tail(right), f, seed)[i - 1]);

                                //  
                                var x := computeAll(tail(p), tail(left), tail(right), f, seed);
                                calc == {
                                    computeAll(p, left, right, f, seed)[i];
                                    ([ f(first(left), first(x))] + x)[i];
                                    x[i - 1];
                                    nodeAt(take(tail(p), i - 1), rc).v;
                                    { simplifyNodeAtIndexFirstBit(p, r, i) ; }
                                    nodeAt(take(p, i), r).v;
                                }
                            }
                        } else {    
                            // i = 0, the node is the root
                            calc == {
                                nodeAt(take(p, 0), r).v;
                                nodeAt([], r).v;
                                r.v;
                                { computeRootLeftRightIsCorrectForTree(p, r, left, right, f, seed) ; }
                                computeRootLeftRight(p, left, right, f, seed);
                                computeAllUp2(p, left, right, f, seed)[0];
                                { computeAllUpEqualsComputeAll(p, left, right, f, seed); }
                                computeAll(p, left, right, f, seed)[0];
                            }
                        }
            }
            
        }
    }
 }