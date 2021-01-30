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

include "../helpers/SeqHelpers.dfy"
include "../paths/PathInCompleteTrees.dfy"
include "../seqofbits/SeqOfBits.dfy"
include "../trees/CompleteTrees.dfy"
include "../trees/Trees.dfy"

/**
 *  Provide simple results on computation of root value of a synthesised attribute
 *  on a tree.
 *
 *  1. `computeRootPath` that computes the root value from siblings and seed. 
 *  2. `computeRootLeftRight` refines `computeRootPath` vy splitting siblings into left and right.
 *  3. `computeRootLeftRightIsCorrectForTree` shows that `computeRootLeftRight` computes the root value of
 *      the tree.
 */
module GenericComputation {
 
    import opened SeqHelpers
    import opened PathInCompleteTrees
    import opened SeqOfBits
    import opened CompleteTrees
    import opened Trees

    ///////////////////////////////////////////////////////////////////////////
    //  Main algorithms
    ///////////////////////////////////////////////////////////////////////////

    /**
     *  Compute the value of attribute `f` given a path, seed and values on siblings.
     *  
     *  @param  p       A path.
     *  @param  b       The value of `f` on each sibling of a node on the path.
     *  @param  f       The binary operation to compute.
     *  @param  seed    The value at the end of the path.
     *  @returns        The value of `f` synthesised on `p`.
     */
    function computeRootPath<T>(p : seq<bit>, b : seq<T>, f : (T,T) -> T, seed: T) : T
        requires |p| == |b|
        decreases p
    {
        if |p| == 0 then 
            seed
        else 
            var r := computeRootPath(tail(p), tail(b), f, seed);
            if first(p) == 0 then
                f(r, first(b))
            else 
                f(first(b), r)
    }

    /**
     *  Compute the value of attribute `f` on a path given siblings splitted into left and right.
     *  
     *  @param  p       A path.
     *  @param  left    The value of `f` on each left sibling.
     *  @param  right   The value of `f` on each right sibling.
     *  @param  f       The binary operation to compute.
     *  @param  seed    The value at the end of the path.
     *  @returns        The value of `f` synthesised on `p`.
     */
    function computeRootLeftRight<T>(p : seq<bit>, left : seq<T>, right: seq<T>, f : (T,T) -> T, seed: T) : T
        requires |p| == |left| == |right|

        /** This function computes the same as  `computeRootPath`. */
        ensures 
            computeRootLeftRight(p, left, right, f, seed) 
            == 
            var b :=  zipCond(p, right, left);
            computeRootPath(p, b, f, seed)

        decreases p
    {
        if |p| == 0 then 
            seed
        else 
            var r := computeRootLeftRight(tail(p), tail(left), tail(right), f, seed);
            if first(p) == 0 then
                f(r, first(right))
            else 
                f(first(left), r)
    }

    ///////////////////////////////////////////////////////////////////////////
    //  Main correctness proof.
    ///////////////////////////////////////////////////////////////////////////

    /**
     *  The value computed by computeRootPath is the same as the value of the root
     *  of the tree.
     *
     *  @param  p       A path.
     *  @param  r       A tree.
     *  @param  left    The value of `f` on siblings on path `p`.
     *  @param  right   The value of `f` on siblings on path `p`.
     *  @param  f       A binary operation.
     *  @param  seed    A value.
     */
    lemma {:induction p, r} computeRootLeftRightIsCorrectForTree<T>(p : seq<bit>, r : Tree<T>, left : seq<T>, right: seq<T>, f : (T,T) -> T, seed: T) 

        requires |p| == height(r) 
        requires isCompleteTree(r)
        requires isDecoratedWith(f, r)

        requires seed == nodeAt(p, r).v
        requires |right| == |left| == |p|

        /** Left and right contains siblings left and right values.  */
        requires forall i :: 0 <= i < |p| ==>
            siblingAt(take(p, i + 1), r).v == 
                if p[i] == 0 then 
                    right[i]
                else 
                    left[i]
          
        ensures r.v == computeRootLeftRight(p, left, right, f, seed)

    {
        //  As computeRootLeftRight computes the same as computeRootPath(p, b, f, seed)
        //  for b == zipCond(p, right, left) we can use the lemma `computeOnPathYieldsRootValue`
        var b := zipCond(p, right, left);
        computeOnPathYieldsRootValue(p, r, b, f, seed);
    }    

    ///////////////////////////////////////////////////////////////////////////
    //  Helpers lemmas.
    ///////////////////////////////////////////////////////////////////////////

    /**
     *  If a seq of values b corresponds to the values of siblings on a path,
     *  then p[1..] corresponds to siblings of lc or rc depending on p[0].
     *
     *  @param  p       A path.
     *  @param  r       A complete tree. 
     *  @param  b       The value of `f` on each sibling of a node on the path.
     */
    lemma {:induction r} projectValuesOnChild<T>(p : seq<bit>, r : Tree<T>, b : seq<T>)  
        requires 1 <= |p| <= height(r) 
        requires isCompleteTree(r)
        requires |b| == |p|
        requires forall k :: 0 <= k < |b| ==> b[k] == siblingAt(take(p, k + 1), r).v
        /** Depending on p[0], `b` projects onto `lc or `rc`. */
        ensures match r
            case Node(_, lc, rc) =>
                forall k :: 0 <= k < |tail(p)| ==>
                     tail(b)[k] == siblingAt(take(tail(p), k + 1), if first(p) == 0 then lc else rc).v
    {
        match r 
            case Node(_, lc, rc) => 
                forall (k : nat | 0 <= k < |tail(b)|) 
                    ensures 
                        0 <= k < |tail(b)|  ==> 
                             tail(b)[k] == siblingAt(take(tail(p), k + 1), if first(p) == 0 then lc else rc).v 
                {
                    if ( k == 0 ) {
                        //  for k == 0, we cannot use the simplification on first bit of path
                        //  for siblings, so we do it case by case.
                        if |p| == 1 {
                            //  Thanks Dafny.
                        } else {
                            //  We need to prove b[1..][0] == siblingAt(p[1..][..0 + 1], if p[0] == 0 then lc else rc).v

                            var child := if first(p) == 0 then lc else rc;
                            calc == {
                                    [] + [1];
                                    [1];
                                }
                            calc == {
                                siblingAt(take(tail(p), 0 + 1), child).v;
                                siblingAt(take(tail(p), 1), child).v;
                                siblingAt([p[1]], child).v;
                                nodeAt([] + [1 - p[1]], child).v;
                                nodeAt([1 - p[1]], child).v;
                                nodeAt([p[0], 1 - p[1]], r).v;
                                siblingAt([p[0] , p[1]], r).v;
                                tail(b)[0];
                            }
                        }
                    } else {
                        assert( k >= 1 );
                        var child := if first(p) == 0 then lc else rc ;
                        calc == {   //  These terms are equal
                            tail(b)[k] ;
                            b[k + 1];
                            siblingAt(take(p, k + 1 + 1), r).v;
                            { simplifySiblingAtFirstBit(take(p, k + 1 + 1), r) ; }
                            siblingAt(tail(take(p, k + 1 + 1)), child).v;
                            { seqIndexLemmas(p, k + 2); } 
                            siblingAt(take(tail(p), k + 1), child).v;
                        }
                    }
                }
    }

    /**
     *  Extend `projectValuesOnChild` when siblings are split into leftand right.
     *  @param  p       A path.
     *  @param  r       A tree.
     *  @param  left    The value of `f` on siblings on path `p`.
     *  @param  right   The value of `f` on siblings on path `p`.
     */
    lemma {:induction r} projectLeftRightValuesOnChild<T>(p : seq<bit>, r : Tree<T>, left : seq<T>, right: seq<T>)  
        requires 1 <= |p| <= height(r) 
        requires isCompleteTree(r)
        requires |left| == |right| == |p|
        requires forall k :: 0 <= k < |p| ==> 
            siblingAt(take(p, k + 1), r).v ==  
                if p[k] == 0 then 
                    right[k]
                else 
                    left[k]
        /** Depending on p[0], `b` projects onto `lc or `rc`. */
        ensures match r
            case Node(_, lc, rc) =>
                forall k :: 0 <= k < |tail(p)| ==>
                    siblingAt(take(tail(p), k + 1), if first(p) == 0 then lc else rc).v
                    == 
                    if tail(p)[k] == 0 then 
                        tail(right)[k]
                    else 
                        tail(left)[k]
    {
        //  for b == zipCond(p, right, left) we can use the lemma `projectValuesOnChild`
        var b := zipCond(p, right, left);
        projectValuesOnChild(p, r, b);   
        assert(tail(b) == zipCond(tail(p), tail(right), tail(left)));        
    }

    /**
     *  The value computed by computeRootPath is the same as the value of the root
     *  of the tree, for a complete tree decorated with `f`.
     *
     *  @param  p       A path.
     *  @param  r       A tree.
     *  @param  b       The values on the siblings of nodes on path `p`.
     *  @param  f       A binary operation.
     *  @param  seed    A value (at the end of the path).
     */
    lemma {:induction p, r, b} computeOnPathYieldsRootValue<T>(p : seq<bit>, r : Tree<T>, b : seq<T>, f : (T,T) -> T, seed: T) 
        requires |p| == height(r) 
        requires isCompleteTree(r)
        /** `r` is decorated with attribute `f`. */
        requires isDecoratedWith(f, r)
        /** Seed is the value at the leaf of the path `p`. */
        requires seed == nodeAt(p, r).v
        requires |b| == |p|
        /** `b` contains values at siblings on path `p`. */
        requires forall i :: 0 <= i < |b| ==> b[i] == siblingAt(take(p, i + 1), r).v

        /** computeRootPath computes the value of the root.  */
        ensures r.v == computeRootPath(p, b, f, seed)

        decreases p
    {
        if |p| == 0 {
            //  Thanks Dafny
        } else {  
            match r
                case Node(_, lc, rc) =>

                //  By definition r.v == f(lc.v, rc.v)
                //  We show that whatever child is on path `p`  we have the value of the sibling.

                var child := if first(p) == 0 then lc else rc ;
                var a := if first(p) == 0 then 1 else 0;

                //  This ensures we can use computeOnPathYieldsRootValue inductively
                //  Tt proves that tail(b)[i] == siblingAt(take(tail(p), i + 1), r).v
                projectValuesOnChild(p, r, b);
                
                //  Induction on lc or rc depending on p[0]
                computeOnPathYieldsRootValue(tail(p), child, tail(b), f, seed);
                // This implies that if first(p) == 0 then lc.v else rc.v  

                calc == {
                    b[0] ;
                    nodeAt([] + [a], r).v;
                    calc == {  //  simplify
                        [] + [a];
                        [a];
                    }
                    nodeAt([a], r).v;
                    (if first(p) == 0 then rc.v else lc.v);
                }
        }
    }

 }