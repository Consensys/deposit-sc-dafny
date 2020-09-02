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
        var i := 0;
        var k' : nat := k;

        r := seed ;
        next := [] ; 

        ghost var h1 : nat := h;
        ghost var (r', next') := computeRootPathDiffAndLeftSiblingsUpv4d(h, k, valOnLeftAt, seed, []);

        //  compute natToBitList(k, h)
        ghost var p : seq<bit> := [];

        //  need this fact to prove main loop invariant holds on entry
        assert(valOnLeftAt == take(valOnLeftAt, h - i));

        while (i < h && k' % 2 == 1)

            invariant 0 <= i <= h
            invariant i == |take(valOnLeftAt, i)|
            invariant 0 <= k' < power2(h1)
            invariant h1 == h - i
            //  Main invariant
            invariant (r', next') == 
                computeRootPathDiffAndLeftSiblingsUpv4d(h1, k', take(valOnLeftAt, h1), r, next);

            //  p invariant
            invariant |p| == i
            invariant forall k :: 0 <= k < |p| ==> p[k] == 1

            //  Value of natToBitList2(k, h)
            invariant natToBitList2(k, h) == natToBitList2(k', h1) + p

            decreases h - i 
        { 
            p := [1] + p;
            next := [valOnLeftAt[h - i - 1]] + next ;
            r := diff(valOnLeftAt[h - i - 1], r);
            //  the following is used to prove the main invariant
            // assert(valOnLeftAt[..h1 - 1] == valOnLeftAt[..h1][..h1 - 1]);
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

 }