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

include "IncAlgoV2.dfy"
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

module IncAlgoV3 {
 
    import opened DiffTree
    import opened IncAlgoV2
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
     *  Compute the root value and the left siblings of next path concurrently.
     *  This version has two additional variables:
     *  1. k constrained to be the integer that corresponds to path `p`.
     *  2. h which is the size of the path.
     *
     *  This version is decorated with assertions relating `p` and k and h,
     *  in order to replace p by k in V4.
     */
    function  computeRootPathDiffAndLeftSiblingsUpv3(
        p : seq<bit>, 
        h : nat,
        k : nat,
        valOnLeftAt : seq<int>, seed: int) : (int, seq<int>)
        requires h == |p| == |valOnLeftAt| 
        requires |p| >= 1

        requires k < power2(|p|)
        requires natToBitList(k, |p|) == p
        
        /**
         *  V3 and V2 compute same result.
         */
        ensures computeRootPathDiffAndLeftSiblingsUpv3(p, h, k, valOnLeftAt, seed) ==
            computeRootPathDiffAndLeftSiblingsUpv2(p, valOnLeftAt, seed)

        decreases p
    {
     if |p| == 1 then
        assert( k == first(p) as nat);
        assert( h == |p|);
        var r := computeRootPathDiff(p, valOnLeftAt, seed);
        (r, if first(p) == 0 then [seed] else valOnLeftAt) 
    else 
        if last(p) == 0 then
            assert( k % 2 == 0);
            assert( h == |p|);
            (
                computeRootPathDiffUpv2(init(p), h - 1, k / 2, init(valOnLeftAt), diff(seed, 0)),
                init(valOnLeftAt) + [seed]
            )
        else      
            assert( k % 2 == 1);
            assert( h == |p|);
            var r :=  computeRootPathDiffAndLeftSiblingsUpv3(
                    init(p), 
                    h - 1,
                    k / 2,
                    init(valOnLeftAt),  
                    diff(last(valOnLeftAt), seed));
                    (r.0, r.1 + [last(valOnLeftAt)])
    }

    /**
     *  Use the natural value of a path and height (supposedly of the tree) 
     *  to compute the results.
     */
    function method computeRootPathDiffAndLeftSiblingsUpv4(
        h : nat,
        k : nat,
        valOnLeftAt : seq<int>, seed: int) : (int, seq<int>)
        requires 1 <= h == |valOnLeftAt|
        requires k < power2(h)

        /**
         *  V4 and V3 compute same result.
         */
        ensures 
            computeRootPathDiffAndLeftSiblingsUpv4(h, k, valOnLeftAt, seed) ==
            var p := natToBitList(k, h);
            computeRootPathDiffAndLeftSiblingsUpv3(p, h, k, valOnLeftAt, seed) 

        decreases h
    {
        if h == 1 then
            var r := computeRootPathDiff([k as bit], valOnLeftAt, seed);
            assert(valOnLeftAt ==  [valOnLeftAt[0]]);
            (r, if k == 0 then [seed] else [last(valOnLeftAt)]) 
        else 
            if k % 2 == 0 then
                (
                    computeRootPathDiffUpv3(h - 1, k / 2, init(valOnLeftAt), diff(seed, 0)),
                    init(valOnLeftAt) + [seed]
                )
            else      
                var r :=  computeRootPathDiffAndLeftSiblingsUpv4(
                        h - 1,
                        k / 2,
                        init(valOnLeftAt),  
                        diff(last(valOnLeftAt), seed));
                (r.0, r.1 + [last(valOnLeftAt)])
    }

    /**
     *  For path of size >= 2, computeRootPathDiffAndLeftSiblingsUp and computeRootPathDiffUp
     *  yield the same result.
     */
    lemma  computeRootAndSiblingsV4IsCorrect(h : nat,
        k : nat,
        valOnLeftAt : seq<int>, seed: int)
        requires 1 <= h == |valOnLeftAt|
        requires k < power2(h)

        ensures  computeRootPathDiffAndLeftSiblingsUpv4(h, k, valOnLeftAt, seed) == 
            (computeRootPathDiffUp(natToBitList(k, h), valOnLeftAt, seed),
            computeLeftSiblingOnNextPath(natToBitList(k, h), computeAllPathDiffUp(natToBitList(k, h), valOnLeftAt, seed), valOnLeftAt)
            )

        
    {   
        /*
         *  V4 computes same as V3, same as V2 and V2 is correct.
         */
        calc == {
            computeRootPathDiffAndLeftSiblingsUpv4(h, k, valOnLeftAt, seed);
            computeRootPathDiffAndLeftSiblingsUpv3(natToBitList(k, h), h, k, valOnLeftAt, seed);
            computeRootPathDiffAndLeftSiblingsUpv2(natToBitList(k, h), valOnLeftAt, seed);
            {
                computeRootAndSiblingsv2IsCorrect(natToBitList(k, h),  valOnLeftAt, seed);
            }
            (computeRootPathDiffUp(natToBitList(k, h), valOnLeftAt, seed),
            computeLeftSiblingOnNextPath(natToBitList(k, h), 
                computeAllPathDiffUp(natToBitList(k, h), valOnLeftAt, seed), valOnLeftAt));
        }   
    }

   /**
     *  Use the natural value of a path and height (supposedly of the tree) 
     *  to compute the results. Stop at h == 0 instead of h == 1. 
     */
    function method computeRootPathDiffAndLeftSiblingsUpv4b(
        h : nat,
        k : nat,
        valOnLeftAt : seq<int>, seed: int) : (int, seq<int>)
        requires 0 <= h == |valOnLeftAt|
        requires k < power2(h)

        decreases h
    {
        if h == 0 then
            (seed, [])
        else 
            if k % 2 == 0 then
                (
                    computeRootPathDiffUpv3(h - 1, k / 2, init(valOnLeftAt), diff(seed, 0)),
                    init(valOnLeftAt) + [seed]
                )
            else      
                var r :=  computeRootPathDiffAndLeftSiblingsUpv4b(
                        h - 1,
                        k / 2,
                        init(valOnLeftAt),  
                        diff(last(valOnLeftAt), seed));
                (r.0, r.1 + [last(valOnLeftAt)])
    }

    lemma  computeRootAndSiblingsV4bIsCorrect(h : nat,
        k : nat,
        valOnLeftAt : seq<int>, seed: int)
        requires h == |valOnLeftAt|
        requires k < power2(h)

        ensures  h >= 1 ==> computeRootPathDiffAndLeftSiblingsUpv4b(h, k, valOnLeftAt, seed) == 
           computeRootPathDiffAndLeftSiblingsUpv4(h, k, valOnLeftAt, seed)
    {
        if ( h >= 2 ) {
            //  if h >= 2 they compute exactly the same. Thanks Dafny
        } else if (h == 1) {
            //  The only interesting case is h == 1
            //  If h == 1 then k == 0 or k == 1. We show that v4b computes same as v4
            //  by unfolding the computation.
            if (k % 2 == 0) {
                var r := computeRootPathDiffAndLeftSiblingsUpv4b(0, 0, [], diff(seed, 0));

                calc == {
                    computeRootPathDiffAndLeftSiblingsUpv4b(h, k, valOnLeftAt, seed);
                    (r.0, init(valOnLeftAt) + [seed]);    
                    calc == {
                        [] + [seed];
                        [seed];
                    }
                    (r.0, [seed]);
                    calc == {
                        r.0;
                        diff(seed, 0);
                    }
                    (diff(seed, 0), [seed]);
                    (computeRootPathDiff([0], valOnLeftAt, seed), [seed]);
                }
            } else {
                //   k % 2 == 1 and k == 1
                var r := computeRootPathDiffAndLeftSiblingsUpv4b(0, 0, [], diff(valOnLeftAt[0], seed));
                calc {
                    computeRootPathDiffAndLeftSiblingsUpv4b(h, k, valOnLeftAt, seed);
                    (r.0, r.1 + [last(valOnLeftAt)]);
                    calc == {
                        r.1 + [last(valOnLeftAt)];
                        [] + [last(valOnLeftAt)];
                        [last(valOnLeftAt)];
                    }
                    (r.0, [last(valOnLeftAt)]);
                    (diff(last(valOnLeftAt), seed), [last(valOnLeftAt)]);
                    (computeRootPathDiff([1], valOnLeftAt, seed),  [last(valOnLeftAt)]);
                }
            }
        }
    }

    /**
     *  Tail recursive version of algorithm with accumulator newLeft.
     *  Add a bit to indicate whether left siblings have to computed or whether
     *  we can skip this step.
     */
    function method computeRootPathDiffAndLeftSiblingsUpv4d(
        h : nat,
        k : nat,
        valOnLeftAt : seq<int>, 
        seed: int,
        newLeft : seq<int>) : (int, seq<int>)
        requires 0 <= h == |valOnLeftAt|
        requires k < power2(h)

        decreases h

    {
        if h == 0 then
            (seed, newLeft)
        else 
            if k % 2 == 0 then
                (
                    computeRootPathDiffUpv3(h - 1, k / 2, init(valOnLeftAt), diff(seed, 0)),
                    init(valOnLeftAt) + [seed] + newLeft
                )
            else      
                computeRootPathDiffAndLeftSiblingsUpv4d(
                        h - 1,
                        k / 2,
                        init(valOnLeftAt),  
                        diff(last(valOnLeftAt), seed),
                        [last(valOnLeftAt)] + newLeft)
    }

    lemma foo555(h : nat, k : nat, valOnLeftAt : seq<int>, seed: int, newLeft : seq<int>, r : seq<int>) 
        requires 0 <= h == |valOnLeftAt|
        requires k < power2(h)
        ensures computeRootPathDiffAndLeftSiblingsUpv4d(h, k, valOnLeftAt, seed, newLeft + r) ==
            (computeRootPathDiffAndLeftSiblingsUpv4d(h, k, valOnLeftAt, seed, newLeft).0,
            computeRootPathDiffAndLeftSiblingsUpv4d(h, k, valOnLeftAt, seed, newLeft).1 + r)
    {
       
        if h == 0 {
            //  Thanks Dafny
        } else {
            if k % 2 == 0  {
                var r1 :=  computeRootPathDiffAndLeftSiblingsUpv4d(h, k, valOnLeftAt, seed, newLeft);
                var r2 :=  computeRootPathDiffAndLeftSiblingsUpv4d(h, k, valOnLeftAt, seed, newLeft + r);
                //  Show that r1 == r2
                assert(r1.0 == r2.0);
                calc == {
                    r2.1;
                    init(valOnLeftAt) + [seed] + (newLeft + r);
                    r1.1 + r;
                }
            } else {
               
                var r1 :=  computeRootPathDiffAndLeftSiblingsUpv4d(h, k, valOnLeftAt, seed, newLeft);
                var r2 :=  computeRootPathDiffAndLeftSiblingsUpv4d(h, k, valOnLeftAt, seed, newLeft + r);
                calc == {
                    computeRootPathDiffAndLeftSiblingsUpv4d(h, k, valOnLeftAt, seed, newLeft + r);
                    computeRootPathDiffAndLeftSiblingsUpv4d(
                        h - 1,
                        k / 2,
                        init(valOnLeftAt),  
                        diff(last(valOnLeftAt), seed),
                        [last(valOnLeftAt)] + (newLeft + r));
                    calc == {
                         [last(valOnLeftAt)] + (newLeft + r);
                        ([last(valOnLeftAt)] + newLeft) + r;
                    }
                    computeRootPathDiffAndLeftSiblingsUpv4d(
                        h - 1,
                        k / 2,
                        init(valOnLeftAt),  
                        diff(last(valOnLeftAt), seed),
                        ([last(valOnLeftAt)] + newLeft) + r);
                    { foo555(h - 1, k / 2, init(valOnLeftAt), diff(last(valOnLeftAt), seed), [last(valOnLeftAt)] + newLeft, r ); }
                    (
                    computeRootPathDiffAndLeftSiblingsUpv4d(h - 1, k / 2, init(valOnLeftAt), diff(last(valOnLeftAt), seed), [last(valOnLeftAt)] + newLeft).0,
                    computeRootPathDiffAndLeftSiblingsUpv4d(h - 1, k / 2,  init(valOnLeftAt), diff(last(valOnLeftAt), seed), [last(valOnLeftAt)] + newLeft).1 + r
                    );
                    (
                        r1.0,
                        r1.1 + r
                    );
                }
            }
        }
    }

    /**
     *  Correctness proof of tail recursive version.
     */
    lemma  {:induction h} computeRootAndSiblingsV4dIsCorrect(h : nat,
        k : nat,
        valOnLeftAt : seq<int>, seed: int,  newLeft : seq<int>)
        requires 1 <= h == |valOnLeftAt|
        requires k < power2(h)

        ensures  computeRootPathDiffAndLeftSiblingsUpv4b(h, k, valOnLeftAt, seed) == 
           computeRootPathDiffAndLeftSiblingsUpv4d(h, k, valOnLeftAt, seed, [])
    {   
        if h == 1 {
            if (k % 2 == 0) {
                //  A little help
                calc {
                    init(valOnLeftAt) + [seed] + [];
                    init(valOnLeftAt) + [seed];
                }
            } else {
                //  h == 1 and k % 2 == 1
                //  use definitions of the functions.
                var r :=  computeRootPathDiffAndLeftSiblingsUpv4b(0, 0, init(valOnLeftAt), diff(last(valOnLeftAt), seed));
                calc == {
                    r;
                    computeRootPathDiffAndLeftSiblingsUpv4b(0, 0, init(valOnLeftAt), diff(last(valOnLeftAt), seed));

                    (diff(last(valOnLeftAt), seed), []);
                }   
                //  Result of computeRootPathDiffAndLeftSiblingsUpv4b using r:
                calc == {
                    computeRootPathDiffAndLeftSiblingsUpv4b(1, 1, valOnLeftAt, seed);
                    (r.0, r.1 + [last(valOnLeftAt)]);
                    calc == {
                        [last(valOnLeftAt)];
                        [] + [last(valOnLeftAt)];
                    }
                    (diff(last(valOnLeftAt), seed), [last(valOnLeftAt)]);
                }
                //  Result of computeRootPathDiffAndLeftSiblingsUpv4d
                calc == {
                    computeRootPathDiffAndLeftSiblingsUpv4d(1, 1, valOnLeftAt, seed, []);
                    computeRootPathDiffAndLeftSiblingsUpv4d(0, 0, init(valOnLeftAt), diff(last(valOnLeftAt), seed), [last(valOnLeftAt)] + []);
                    calc == {
                         [last(valOnLeftAt)] + [];
                         [last(valOnLeftAt)];
                    }
                    (diff(last(valOnLeftAt), seed), [last(valOnLeftAt)]);
                } 
            }
        } else {
            if k % 2 == 0 {
                //  Thanks Dafny
                 calc {
                        init(valOnLeftAt) + [seed] + [];
                        init(valOnLeftAt) + [seed];
                }
            } else {
                // k % 2 == 1, h >= 2
                //  result of 4b
                var r1:= computeRootPathDiffAndLeftSiblingsUpv4b(h, k, valOnLeftAt, seed);
                var r :=  computeRootPathDiffAndLeftSiblingsUpv4b(
                        h - 1,
                        k / 2,
                        init(valOnLeftAt),  
                        diff(last(valOnLeftAt), seed));
                //  Result of 4b
                assert(r1 == (r.0, r.1 + [last(valOnLeftAt)]));

                //  Result of 4d
                // computeRootPathDiffAndLeftSiblingsUpv4d(h, k, valOnLeftAt, seed, [])
                var r' := computeRootPathDiffAndLeftSiblingsUpv4d(
                        h - 1,
                        k / 2,
                        init(valOnLeftAt),  
                        diff(last(valOnLeftAt), seed),
                        [last(valOnLeftAt)] + []);
                assert(r' == computeRootPathDiffAndLeftSiblingsUpv4d(h, k, valOnLeftAt, seed, []));
                
                //  Induction on h - 1, k / 2
                computeRootAndSiblingsV4dIsCorrect(h - 1, k / 2,  init(valOnLeftAt),
                                    diff(last(valOnLeftAt), seed),  [last(valOnLeftAt)]);
                assert (
                    computeRootPathDiffAndLeftSiblingsUpv4b(h - 1, k / 2,  init(valOnLeftAt), diff(last(valOnLeftAt), seed)) ==
                    computeRootPathDiffAndLeftSiblingsUpv4d(h - 1, k / 2,  init(valOnLeftAt), diff(last(valOnLeftAt), seed), [])
                    );

                //  Show that r1 == r'
                calc == {
                    r.0;
                    computeRootPathDiffAndLeftSiblingsUpv4b(h - 1, k / 2, init(valOnLeftAt),diff(last(valOnLeftAt), seed)).0;
                    computeRootPathDiffAndLeftSiblingsUpv4d(h - 1, k / 2,  init(valOnLeftAt), diff(last(valOnLeftAt), seed), []).0;
                    { foo555(h - 1, k / 2, init(valOnLeftAt), diff(last(valOnLeftAt), seed), [], [last(valOnLeftAt)]);}
                    computeRootPathDiffAndLeftSiblingsUpv4d(h - 1, k / 2,  init(valOnLeftAt), diff(last(valOnLeftAt), seed), [] + [last(valOnLeftAt)]).0;
                     calc {
                         [last(valOnLeftAt)] + [];
                         [] + [last(valOnLeftAt)];
                     }
                    r'.0;
                }

                calc == {
                    r.1 + [last(valOnLeftAt)];
                     computeRootPathDiffAndLeftSiblingsUpv4b(h - 1, k / 2, init(valOnLeftAt),diff(last(valOnLeftAt), seed)).1 + [last(valOnLeftAt)] ;
                     // Induction
                     computeRootPathDiffAndLeftSiblingsUpv4d(h - 1, k / 2,  init(valOnLeftAt), diff(last(valOnLeftAt), seed), []).1 + [last(valOnLeftAt)];
                     { foo555(h - 1, k / 2, init(valOnLeftAt), diff(last(valOnLeftAt), seed), [], [last(valOnLeftAt)]);}
                    computeRootPathDiffAndLeftSiblingsUpv4d(h - 1, k / 2,  init(valOnLeftAt), diff(last(valOnLeftAt), seed), [] + [last(valOnLeftAt)]).1   ;
                     calc {
                         [last(valOnLeftAt)] + [];
                         [] + [last(valOnLeftAt)];
                     }
                     r'.1;
                }
            }
        }
    }
   
 }