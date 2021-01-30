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

include "../synthattribute/ComputeRootPath.dfy"
include "../synthattribute/RightSiblings.dfy"
include "../synthattribute/Siblings.dfy"
include "../paths/NextPathInCompleteTreesLemmas.dfy"
include "../seqofbits/SeqOfBits.dfy"
include "../helpers/SeqHelpers.dfy"

/**
 *  Provide a nice result: compute root with values of left siblings or left siblings on 
 *  next path gives the same result!
 */
module CommuteProof {

    import opened ComputeRootPath
    import opened RSiblings
    import opened Siblings
    import opened NextPathInCompleteTreesLemmas
    import opened SeqOfBits
    import opened SeqHelpers

    /**
     *  Computing root value with left siblings or left siblings on next path yields same
     *  result.
     *
     *  This is the main reason why the deposit smart contract algorothm is correct.
     *
     *  @param  p   A path.
     *  @param  left        The values of the left siblings of nodes on path `p`.
     *  @param  right       The values of the right siblings of nodes on path `p`.
     *  @param  f           The binary operation to compute.
     *  @param  seed        The value at the end of the path.     
     *
     */
    lemma {:induction p, left, right, seed} computeRootAndUpdateLeftSiblingsCommutes<T>(p: seq<bit>, left : seq<T>, right: seq<T>, f  : (T, T) -> T, seed : T)
        requires 1 <= |p| == |left| == |right|
        ensures 
            computeRootLeftRightUp(p, left, right, f, seed) ==
                computeRootLeftRightUp(p, computeLeftSiblingOnNextPathFromLeftRight(p, left, right, f, seed), right, f, seed)           
            
    {   //  Thanks Dafny
    }

    /** 
     *  If the right vector is the zeroes that correspond to d, then
     *  the root value can be computed using the siblings on next path only 
     *  and without the seed value! That's where the magic happens as if we update
     *  the compute the left siblings on next path (using the seed), we do not need 
     *  to remember it to get the root value.
     *
     *  @param  p           A path.
     *  @param  left        The values of the left siblings of nodes on path `p`.
     *  @param  right       The values of the right siblings of nodes on path `p`.
     *  @param  f           The binary operation to compute.
     *  @param  seed        The value at the end of the path.    
     */
    lemma {:induction p, left, right} computeRootUsingNextPath<T>(p: seq<bit>, left : seq<T>, right: seq<T>, f  : (T, T) -> T, seed : T, d: T)
        requires 1 <= |p| == |left| == |right|
        requires exists i :: 0 <= i < |p| && p[i] == 0 
        requires right == zeroes(f, d, |p| - 1)
        ensures computeRootLeftRightUp(p, left, right, f, seed) ==
            computeRootLeftRightUp(nextPath(p), computeLeftSiblingOnNextPathFromLeftRight(p, left, right, f, seed), right, f, d) 
        decreases p 
    {
        if |p| == 1 {
            //  Thanks
        } else {
            //  |p| >= 2
            if last(p) == 0 {
                //  Thanks Dafny 
            } else {
                //  To use induction we need to show that pre-conditons are satisfied on init(p)
                //  last(p) != 0 so there must be a zero in init(p)
                pushExistsToInitPrefixIfNotLast(p);
                assert(exists i :: 0 <= i < |init(p)| && init(p)[i] == 0 );
                //  also init(right) == zeroes(f,d, init(p) - 1)
                shiftZeroesPrefix(|p| - 1, f, d);
                assert(init(right) == zeroes(f, f(d, d), |init(p)| - 1));
                
                //  Using induction hypothesis we get the following equality for the lefthand side:
                calc == {
                    computeRootLeftRightUp(p, left, right, f, seed);
                    computeRootLeftRightUp(init(p), init(left), init(right), f, f(last(left), seed));
                    //  induction 
                    { computeRootUsingNextPath(init(p), init(left), init(right), f, f(last(left), seed), f(d, d)); }
                    computeRootLeftRightUp(nextPath(init(p)), computeLeftSiblingOnNextPathFromLeftRight(init(p), init(left), init(right), f, f(last(left), seed)), init(right), f, f(d, d)) ;
                }

                // By definition of nextPath for last(p) == 1
                assert(nextPath(p) == nextPath(init(p)) + [0]);

                //  Now we show that the righthand side is also equal to this last value:
                calc == {
                     computeRootLeftRightUp(nextPath(p), computeLeftSiblingOnNextPathFromLeftRight(p, left, right, f, seed), right, f, d) ;
                     calc == {
                         nextPath(p);
                         // By definition of nextPath for last(p) == 1
                         nextPath(init(p)) + [0];
                     }
                     computeRootLeftRightUp(nextPath(init(p)) + [0], computeLeftSiblingOnNextPathFromLeftRight(p, left, right, f, seed), right, f, d) ;
                     calc == {
                         init(nextPath(init(p)) + [0]);
                         nextPath(init(p));
                     }
                     computeRootLeftRightUp(nextPath(init(p)) , init(computeLeftSiblingOnNextPathFromLeftRight(p, left, right, f, seed)), init(right), f,  f(d, last(right))) ;
                     { assert(last(right) == d) ; }
                     computeRootLeftRightUp(nextPath(init(p)) , init(computeLeftSiblingOnNextPathFromLeftRight(p, left, right, f, seed)), init(right), f,  f(d, d)) ;
                     calc == {
                          init(computeLeftSiblingOnNextPathFromLeftRight(p, left, right, f, seed));
                            computeLeftSiblingOnNextPathFromLeftRight(init(p), init(left), init(right), f, f(last(left), seed));
                     }
                     computeRootLeftRightUp(nextPath(init(p)) ,  computeLeftSiblingOnNextPathFromLeftRight(init(p), init(left), init(right), f, f(last(left), seed)), init(right), f,  f(d, d)) ;
                }
            }
        }
    }
}