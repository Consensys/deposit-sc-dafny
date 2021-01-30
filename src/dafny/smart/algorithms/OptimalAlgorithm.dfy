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

include "MainAlgorithm.dfy"
include "../trees/CompleteTrees.dfy"
include "../synthattribute/ComputeRootPath.dfy"
include "../seqofbits/SeqOfBits.dfy"
include "../helpers/SeqHelpers.dfy"
include "../trees/Trees.dfy"

/**
 *  Optimal algorithm to compute concurrenly root value and left siblings 
 *  on next path.
 */
module OptimalAlgorithm {
 
    import opened MainAlgorithm
    import opened CompleteTrees
    import opened ComputeRootPath
    import opened SeqOfBits
    import opened SeqHelpers
    import opened Trees

    ///////////////////////////////////////////////////////////////////////////
    //  Main algorithm
    ///////////////////////////////////////////////////////////////////////////

    /**
     *  This version switches to computeRootPathDiffUp only as soon as 
     *  we encounter a path p such that last(p) == 0.
     *
     *  @param  p           The path.
     *  @param  left        The values of the left siblings of nodes on path `p`.
     *  @param  right       The values of the left siblings of nodes on path `p`.
     *  @param  seed        The value at nodeAt(p).
     *  @param  f           The binary operation to compute.
     */
    function computeRootAndLeftSiblingsUpOpt<T>(
        p : seq<bit>, left : seq<T>, right : seq<T>, f : (T, T) -> T, seed: T) : (T, seq<T>)
        requires |p| == |left| == |right|
        requires |p| >= 1

        /** Optimised computes same result as non-optimised and hence is correct by 
            lemma `computeRootAndLeftSiblingsUpCorrectInATree`. */
        ensures 
            computeRootAndLeftSiblingsUp(p, left, right, f, seed)
            == 
            computeRootAndLeftSiblingsUpOpt(p, left, right, f, seed)

        decreases p
    {
     if |p| == 1 then
        var r := computeRootLeftRightUp(p, left, right, f, seed);
        (r, if first(p) == 0 then [seed] else left) 
    else 
        if last(p) == 0 then
            //  This is the optimisation: we switch to computing root value only and not left siblings.
            //  From this point upwards `p` and `nextPath(p)` are the same and have same left siblings.
            var x := computeRootLeftRightUp(init(p), init(left), init(right), f,  f(seed, last(right)));
            (x, init(left) + [seed])
        else      
            var r :=  computeRootAndLeftSiblingsUpOpt(
                    init(p), init(left), init(right), f, f(last(left), seed));
            (r.0, r.1 + [last(left)])
    }

 }