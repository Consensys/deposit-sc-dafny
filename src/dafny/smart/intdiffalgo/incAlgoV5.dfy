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
include "IncAlgoV3.dfy"
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

/**
 *  Imperative version of algorithm.
 */
module IncAlgoV5 {
 
    import opened DiffTree
    import opened IncAlgoV1
    import opened IncAlgoV3
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
     */
    method merkleV1(h : nat, k : nat, valOnLeftAt : seq<int>, seed: int) 
                                                        returns (r : int, next: seq<int>)
        requires 1 <= h == |valOnLeftAt|
        //  make sure k % 2 == 0 at some point
        requires k < power2(h) - 1

        ensures (r, next) == 
            var p := natToBitList(k, h);
            (
                computeRootPathDiffUp(p, valOnLeftAt, seed),
                computeLeftSiblingOnNextPath(p, 
                    computeAllPathDiffUp(p, valOnLeftAt, seed), 
                    valOnLeftAt
                )
        )
    {
        //  Variables used in the lopp
        var i := 0;
        var k' : nat := k;

        //  variables for result
        r := seed ;
        next := [] ; 

        //  variables needed for the proof
        ghost var h1 : nat := h;
        //  What the Result of the computation should be:
        ghost var (r', next') := 
            computeRootPathDiffAndLeftSiblingsUpv4d(h, k, valOnLeftAt, seed, []);
        //  Track the value of natToBitList2(k, h)
        ghost var p : seq<bit> := [];

        //  need this fact to prove main loop invariant holds on entry
        assert(valOnLeftAt == take(valOnLeftAt, h - i));

        while (i < h && k' % 2 == 1)

            //  Guarantee i, h, k' and h1 are in the bounds to ensure
            //  pre-conditions of called functions.
            invariant 0 <= i <= h
            invariant i == |take(valOnLeftAt, i)|
            invariant 0 <= k' < power2(h1)
            invariant h1 == h - i

            //  Main invariant. Expected result is maintained by the loop.
            invariant (r', next') == 
                computeRootPathDiffAndLeftSiblingsUpv4d(h1, k', take(valOnLeftAt, h1), r, next);

            //  p has only ones.
            // invariant |p| == i
            invariant forall k :: 0 <= k < |p| ==> p[k] == 1

            //  Value of natToBitList2(k, h)
            invariant natToBitList2(k, h) == natToBitList2(k', h1) + p

            decreases h - i 
        { 
            p := [1] + p;
            next := [valOnLeftAt[h - i - 1]] + next ;
            r := diff(valOnLeftAt[h - i - 1], r);

            //  The following is needed to prove the main invariant
            calc == {
                take(valOnLeftAt, h1 - 1);
                take(take(valOnLeftAt, h1), h1 - 1);
            }

            i := i + 1;
            k' := k' / 2;
            h1 := h1 - 1;
        }

        assert(
            (r', next') == 
                computeRootPathDiffAndLeftSiblingsUpv4d(h1, k', take(valOnLeftAt, h1), r, next)
        );
        
        //  Use lemma to prove that h1 >= 1
        calc ==> {
            true;
            { foo222(h, h1, k, k', p); }
            h1 >= 1;
        }       
        assert(h1 >= 1);

        assert(k' % 2 == 0);

        //  use path as an interndediate to prove that 
        // r ' ==  computeRootPathDiffUpv3(1, k', take(valOnLeftAt, h1), r) 
        assert( k' < power2(h1));
        ghost var pa : seq<bit> := natToBitList(k', h1);
        calc == {
            r';
            computeRootPathDiffAndLeftSiblingsUpv4d(h1, k', take(valOnLeftAt, h1), r, next).0;
            { computeRootAndSiblingsV4dIsCorrect(h1, k', take(valOnLeftAt, h1), r, next) ; }
            computeRootPathDiffAndLeftSiblingsUpv4b(h1, k', take(valOnLeftAt, h1), r).0 ;
            { computeRootAndSiblingsV4bIsCorrect(h1, k',  take(valOnLeftAt, h1), r) ; }
            computeRootPathDiffAndLeftSiblingsUpv4(h1, k',  take(valOnLeftAt, h1), r).0;
            { computeRootAndSiblingsV4IsCorrect(h1, k', take(valOnLeftAt, h1), r ) ; }
            computeRootPathDiffUp(pa, take(valOnLeftAt, h1), r );
            { v3computesRootPath(h1, k', take(valOnLeftAt, h1), r); }
            computeRootPathDiffUpv3(h1, k', take(valOnLeftAt, h1), r);
        }
       
        //  new invariant should be
        assert( r' ==
            computeRootPathDiffUpv3(h1, k', take(valOnLeftAt, h1), r)
        );
        calc == {
            computeRootPathDiffUpv3(h1, k', take(valOnLeftAt, h1), r);
            calc == {
                init(take(valOnLeftAt, h1));
                take(valOnLeftAt, h1 - 1);
            }
            computeRootPathDiffUpv3(h1 - 1, k' / 2, take(valOnLeftAt, h1 - 1), diff(r, 0));
        }
        //  k' % 2 == 1
        next := take(valOnLeftAt, h - i - 1) + [r] + next ;
        // next := [r] + next ;
        r := diff(r, 0);
        i := i + 1;
        k' := k' / 2;
        h1 := h1 - 1;

        //  next computation is complete
        assert(
            next == next'
        );
       

       assert( r' ==
            computeRootPathDiffUpv3(h1, k', take(valOnLeftAt, h1), r)
        );
        //  Show that computation of root path is OK
        assert(i >= 0);
        //  Now compute root path only
        while ( i < h ) 
            invariant i >= 0;
            invariant 0 <= i <= h
            invariant h1 == h - i
            invariant h1 == |take(valOnLeftAt, h1)|
            invariant k' < power2(h1)
            invariant r' ==  computeRootPathDiffUpv3(h1, k', take(valOnLeftAt, h1), r)

        {
            if k' % 2 == 0 {
                r := diff(r, 0);
            } else {
                r := diff(valOnLeftAt[h - i - 1], r);
            }
            calc == {
                take(valOnLeftAt, h1 - 1);
                take(take(valOnLeftAt, h1), h1 - 1);
            }
            i := i + 1;
            k' := k' / 2;
            h1 := h1 - 1;
            
        }
        assert(r' == r);
        assert(next == next');
        calc == {
            (r, next);
            computeRootPathDiffAndLeftSiblingsUpv4d(h, k, valOnLeftAt, seed, []);
            { computeRootAndSiblingsV4dIsCorrect(h, k, valOnLeftAt, seed, []) ; }
            computeRootPathDiffAndLeftSiblingsUpv4b(h, k, valOnLeftAt, seed);
            { computeRootAndSiblingsV4bIsCorrect(h, k, valOnLeftAt, seed) ; }
            computeRootPathDiffAndLeftSiblingsUpv4(h, k, valOnLeftAt, seed);
            { computeRootAndSiblingsV4IsCorrect(h, k, valOnLeftAt, seed) ; }
            (computeRootPathDiffUp(natToBitList(k, h), valOnLeftAt, seed),
            computeLeftSiblingOnNextPath(natToBitList(k, h), computeAllPathDiffUp(natToBitList(k, h), valOnLeftAt, seed), valOnLeftAt)
            );
        }

    }

    method test1(k : nat, h : nat)
         requires k < power2(h) - 1
    {
        var i := 0;
        var k' : nat := k;
        ghost var p : seq<bit> := [];
        ghost var h1 : nat := h;
        
        while ( i < h && k' % 2 == 1)
            invariant 0 <= i <= h
            invariant 0 <= k' < power2(h1)
            invariant h1 == h - i
            invariant natToBitList2(k, h) == natToBitList2(k', h1) + p
            invariant forall k :: 0 <= k < |p| ==> p[k] == 1
        {
            p := [1] + p;
            i := i + 1;
            k' := k' / 2;
            h1 := h1 - 1;
        }

        //  Loop invariant
        // assert(natToBitList2(k, h) == natToBitList2(k', h1) + p);
        //  now show that h1 >=1 necesserily
        calc ==> {
            // k < power2(h) - 1 && k < power2(h1);
            true;
            { foo222(h, h1, k, k', p); }
            h1 >= 1;
        }
        assert(h1 >= 1);
    }   


    /**
     *  If R2 and R3 hold, then necesseraly h1 >= 1.   
     */
    lemma {:induction h, h1, k} foo222(h: nat, h1: nat, k: nat, k' : nat, p : seq<bit>) 
        requires k < power2(h) - 1
        requires k' < power2(h1)
        requires natToBitList2(k, h) == natToBitList2(k', h1) + p    //  R2
        requires forall k :: 0 <= k < |p| ==> p[k] == 1             //  R3
        ensures  h1 >= 1
    {
        if (h1 == 0) {
            calc == {
                k;
                { bitToNatToBitsIsIdentity(k, h) ;}
                bitListToNat(natToBitList2(k, h));
                bitListToNat(natToBitList2(k', h1) + p);
                bitListToNat(natToBitList2(k', 0) + p);
                bitListToNat([] + p);
                calc == {
                    [] + p;
                    p;
                }
                bitListToNat(p);
                { valueOfSeqOfOnes(p); }
                power2(|p|) - 1;
                power2(h) - 1;
            }
        }
        assert(h1 >= 1);
    }

    class Foo {

        const h : nat;

        /**
         *  The array containing the values on the left of the path to
         *  the current leaf.
         */
        var a : array<int>;

        constructor(hh: nat) 
            requires hh >= 1;
            // ensures valOnLeftAt == a[..]
        {
            h := hh;
            //  Initialise array with zeros
            a := new int[hh](  (x: int) => 0 );
            // valOnLeftAt := a[..];
        }

        // var r : int ;
        // ghost var next : seq<int>;

        // ghost var valOnLeftAt : seq<int> ;

       /**
        *  Slight optimisation.
        */
        method merkleV2(k : nat, seed: int) 
        returns (r : int)

            requires 1 <= h == a.Length 
            requires k < power2(h) - 1

            ensures h == old(h)
            ensures a.Length == old(a.Length)
            ensures (r, a[..]) == 
                var p := natToBitList(k, h);
                var valOnLeftAt := old(a[..]);
                (
                    computeRootPathDiffUp(p, valOnLeftAt, seed),
                    computeLeftSiblingOnNextPath(p, 
                        computeAllPathDiffUp(p, valOnLeftAt, seed), 
                        valOnLeftAt
                    )
            )

            // reads this
            modifies this, a
        {
            ghost var valOnLeftAt := a[..];

            ghost var next : seq<int>;

            //  Variables used in the loop
            var i := 0;
            var k' : nat := k;

            //  variables for result
            r := seed ;
            next := [] ; 

            //  variables needed for the proof
            ghost var h1 : nat := h;
            //  What the Result of the computation should be:
            ghost var (r', next') := 
                computeRootPathDiffAndLeftSiblingsUpv4d(h, k, valOnLeftAt, seed, []);
            //  Track the value of natToBitList2(k, h)
            ghost var p : seq<bit> := [];

            //  need this fact to prove main loop invariant holds on entry
            assert(valOnLeftAt == take(valOnLeftAt, h - i));

            while (k' % 2 == 1)

                //  Guarantee i, h, k' and h1 are in the bounds to ensure
                //  pre-conditions of called functions.
                invariant 0 <= i <= h
                invariant i == |take(valOnLeftAt, i)|
                invariant 0 <= k' < power2(h1)
                invariant h1 == h - i

                //  Main invariant. Expected result is maintained by the loop.
                invariant (r', next') == 
                    computeRootPathDiffAndLeftSiblingsUpv4d(h1, k', take(valOnLeftAt, h1), r, next);

                //  p has only ones.
                // invariant |p| == i
                invariant forall k :: 0 <= k < |p| ==> p[k] == 1

                //  Value of natToBitList2(k, h)
                invariant natToBitList2(k, h) == natToBitList2(k', h1) + p

                //  Array invariant: suffix of a unchanged by the first loop
                invariant a[..]  == valOnLeftAt 
                invariant a[h1..]  == next 

                invariant h == old(h)
                // invariant a[..h1]  == valOnLeftAt[h1..] 

                decreases h - i 
            { 
                p := [1] + p;
                
                next := [valOnLeftAt[h - i - 1]] + next ;
                assert(valOnLeftAt[h - i - 1] == a[h - i - 1]);
                r := diff(a[h - i - 1], r);
                // r := diff(valOnLeftAt[h - i - 1], r);

                //  The following is needed to prove the main invariant
                calc == {
                    take(valOnLeftAt, h1 - 1);
                    take(take(valOnLeftAt, h1), h1 - 1);
                }

                i := i + 1;
                k' := k' / 2;
                h1 := h1 - 1;
            }

            assert(
                (r', next') == 
                    computeRootPathDiffAndLeftSiblingsUpv4d(h1, k', take(valOnLeftAt, h1), r, next)
            );
            
            //  Use lemma to prove that h1 >= 1
            calc ==> {
                true;
                { foo222(h, h1, k, k', p); }
                h1 >= 1;
            }       
            assert(h1 >= 1);
            
            assert(k' % 2 == 0);

            //  use path as an interndediate to prove that 
            // r ' ==  computeRootPathDiffUpv3(1, k', take(valOnLeftAt, h1), r) 
            assert( k' < power2(h1));
            ghost var pa : seq<bit> := natToBitList(k', h1);
            calc == {
                r';
                computeRootPathDiffAndLeftSiblingsUpv4d(h1, k', take(valOnLeftAt, h1), r, next).0;
                { computeRootAndSiblingsV4dIsCorrect(h1, k', take(valOnLeftAt, h1), r, next) ; }
                computeRootPathDiffAndLeftSiblingsUpv4b(h1, k', take(valOnLeftAt, h1), r).0 ;
                { computeRootAndSiblingsV4bIsCorrect(h1, k',  take(valOnLeftAt, h1), r) ; }
                computeRootPathDiffAndLeftSiblingsUpv4(h1, k',  take(valOnLeftAt, h1), r).0;
                { computeRootAndSiblingsV4IsCorrect(h1, k', take(valOnLeftAt, h1), r ) ; }
                computeRootPathDiffUp(pa, take(valOnLeftAt, h1), r );
                { v3computesRootPath(h1, k', take(valOnLeftAt, h1), r); }
                computeRootPathDiffUpv3(h1, k', take(valOnLeftAt, h1), r);
            }
        
            //  new invariant should be
            assert( r' ==
                computeRootPathDiffUpv3(h1, k', take(valOnLeftAt, h1), r)
            );
            calc == {
                computeRootPathDiffUpv3(h1, k', take(valOnLeftAt, h1), r);
                calc == {
                    init(take(valOnLeftAt, h1));
                    take(valOnLeftAt, h1 - 1);
                }
                computeRootPathDiffUpv3(h1 - 1, k' / 2, take(valOnLeftAt, h1 - 1), diff(r, 0));
            }
            //  k' % 2 == 1
            //  Update next with [r] and copy take(valOnLeftAt, h - i - 1)
            next := take(valOnLeftAt, h - i - 1) + [r] + next ;
            r := diff(r, 0);
            i := i + 1;
            k' := k' / 2;
            h1 := h1 - 1;

            //  i can be zero if loop condition is initiallty false
            assert(h == old(h));
            a[h - i] := r;
            assert(a[..h1] == valOnLeftAt[..h1]);
            // assert(a[..] == next);
            // assert(a[..h1 - 1] == valOnLeftAt[..h1 - 1]);

            //  store the value of h1
            // ghost var hh1 := h1 ;

            //  next computation is complete
            assert(
                next == next'
            );
        
            // assert(a[..] == next');

            assert(r' ==
                computeRootPathDiffUpv3(h1, k', take(valOnLeftAt, h1), r)
            );
            //  Show that computation of root path is OK
            assert(i >= 0);
            //  Now compute root path only
            while ( i < h ) 
                invariant i >= 0;
                invariant 0 <= i <= h
                invariant h1 == h - i
                invariant h1 == |take(valOnLeftAt, h1)|
                invariant k' < power2(h1)
                invariant r' ==  computeRootPathDiffUpv3(h1, k', take(valOnLeftAt, h1), r)
                // invariant 0 <= h1 <= a.Length
                // invariant a.Length == h
                // invariant h1 < a.Length
                // invariant a[..hh1 - 1] == take(valOnLeftAt, hh1 - 1)
                // invariant h1 == h - i <= hh1
                invariant h == old(h)

            {
                if k' % 2 == 0 {
                    r := diff(r, 0);
                } else {
                    // assert(h1 - 1 >= 1);
                    // calc == {
                    //     valOnLeftAt[h - i - 1];
                    //     valOnLeftAt[h1 - 1];
                    //     // { seqLemmas(valOnLeftAt); }
                    //     // last(take(valOnLeftAt, h1 - 1));
                    //     calc == {
                    //         valOnLeftAt[h1 - 1];
                    //         last(valOnLeftAt[..h1 - 1]);
                    //     }
                    //     last(valOnLeftAt[..h1 - 1]);
                    //     // last(a[..h1 - 1]);
                    //     // a[h1 -1]; 
                    // }
                    assert(valOnLeftAt[h1 - 1] == a[h1 - 1]);

                    r := diff(a[h - i - 1], r);
                    // r := diff(valOnLeftAt[h - i - 1], r);
                }
                calc == {
                    take(valOnLeftAt, h1 - 1);
                    take(take(valOnLeftAt, h1), h1 - 1);
                }
                i := i + 1;
                k' := k' / 2;
                h1 := h1 - 1;
                
            }
            assert(r' == r);
            assert(next == next');
            calc == {
                (r, next);
                computeRootPathDiffAndLeftSiblingsUpv4d(h, k, valOnLeftAt, seed, []);
                { computeRootAndSiblingsV4dIsCorrect(h, k, valOnLeftAt, seed, []) ; }
                computeRootPathDiffAndLeftSiblingsUpv4b(h, k, valOnLeftAt, seed);
                { computeRootAndSiblingsV4bIsCorrect(h, k, valOnLeftAt, seed) ; }
                computeRootPathDiffAndLeftSiblingsUpv4(h, k, valOnLeftAt, seed);
                { computeRootAndSiblingsV4IsCorrect(h, k, valOnLeftAt, seed) ; }
                (computeRootPathDiffUp(natToBitList(k, h), valOnLeftAt, seed),
                computeLeftSiblingOnNextPath(natToBitList(k, h), computeAllPathDiffUp(natToBitList(k, h), valOnLeftAt, seed), valOnLeftAt)
                );
            }

            assert(r == r');
            assert(a[..] == next);

        }
    }


 }