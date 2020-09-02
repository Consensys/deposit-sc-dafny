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
 
include "../intdiffalgo/DiffTree.dfy"
include "../trees/CompleteTrees.dfy"
include "GenericComputation.dfy"
include "../helpers/Helpers.dfy"
include "LeftSiblings.dfy"
include "../MerkleTrees.dfy"
include "../paths/NextPathInCompleteTreesLemmas.dfy"
include "../paths/PathInCompleteTrees.dfy"
include "../seqofbits/SeqOfBits.dfy"
include "../helpers/SeqHelpers.dfy"
include "../trees/Trees.dfy"

module ComputeRootPath {
 
    import opened DiffTree
    import opened CompleteTrees
    import opened GenericComputation
    import opened Helpers
    import opened LeftSiblings
    import opened MerkleTrees
    import opened NextPathInCompleteTreesLemmas
    import opened PathInCompleteTrees
    import opened SeqOfBits
    import opened SeqHelpers
    import opened Trees

    /**
     *  Same as computeRootPath but uses default value 0 on 
     *  right sibling to compute value at root.
     *  Compute the value on a path recursively by computing on children first.
     */
    function method computeRootPathDiff(p : seq<bit>, b : seq<int>, seed: int) : int
        requires |p| == |b|
        decreases p
    {
        if |p| == 0 then 
            seed
        else 
            var r := computeRootPathDiff(tail(p), tail(b), seed);
            if first(p) == 0 then
                diff(r, 0)
            else 
                diff(first(b), r)
    }

    /**
     *  Restrict computation to path of length >= 1.
     */
     function computeRootPathDiff2(p : seq<bit>, b : seq<int>, seed: int) : int
        requires |p| >= 1
        requires |p| == |b|
        ensures computeRootPathDiff2(p, b, seed) == computeRootPathDiff(p, b, seed)
        decreases p
    {
        if |p| == 1 then 
            computeRootPathDiff(p, b, seed)
        else 
            var r := computeRootPathDiff(tail(p), tail(b), seed);
            if first(p) == 0 then
                diff(r, 0)
            else 
                diff(first(b), r)
    }

    // lemma foo606(p : seq<bit>, b : seq<int>, seed: int)

    /**
     *  Compute computeRootPathDiff by pre-computing the last 
     *  step.
     *  This corresponds to computing the value of the penultimate node on the path
     *  and then use it to compute the value on the prefix path (without the last node).
     */
    lemma {:induction p, b} simplifyComputeRootPathDiffOnLast(p : seq<bit>, b : seq<int>, seed: int) 
        requires 1 <= |p| == |b|
        ensures computeRootPathDiff(p, b, seed) == 
            computeRootPathDiff(
                init(p), init(b), 
                if last(p) == 0 then 
                    diff(seed, 0)
                else 
                    diff(last(b), seed)
                )
    {
        if |p| == 1 {
            // Thanks Dafny
        } else {
            calc == {
                init(tail(p));
                { seqLemmas(p) ; }
                tail(init(p));
            }
            calc == {
                init(tail(b));
                { seqLemmas(b) ; }
                tail(init(b));
            }
            //  Dafny can work out the proof, with hint induction on tail(p), tail(b)
            { simplifyComputeRootPathDiffOnLast(tail(p), tail(b), seed); }
            if first(p) == 0 {
                calc == {
                    computeRootPathDiff(p, b, seed);
                    diff(computeRootPathDiff(tail(p), tail(b), seed), 0);
                    diff(
                        computeRootPathDiff(init(tail(p)),init(tail(b)), 
                            if last(p) == 0 then diff(seed, 0)
                            else diff(last(b), seed)
                        )
                        , 0
                    );
                }
            }
            else {  // first(p) == 1
                calc == {
                    computeRootPathDiff(p, b, seed);
                    diff(first(b), computeRootPathDiff(tail(p), tail(b), seed));
                    diff(
                        first(b),
                        computeRootPathDiff(init(tail(p)), init(tail(b)), 
                            if last(p) == 0 then diff(seed, 0)
                            else diff(last(b), seed)
                        )
                    );
                }            
            }
        }
    }

    /**
     *  Compute root value starting from end of path.
     *  Recursive computation by simplifying the last step of the path i.e.
     *  computing its value and then iterate on the prefix path.
     */
    function computeRootPathDiffUp(p : seq<bit>, b : seq<int>, seed: int) : int
        requires |p| == |b|
        decreases p
    {
     if |p| == 0 then
        seed 
    else 
        if last(p) == 0 then
            computeRootPathDiffUp(init(p), init(b),diff(seed, 0))
        else        
            computeRootPathDiffUp(init(p), init(b),diff(last(b), seed))
    }

    /**
     *  This version mixes the binary representation of a path and the corresponding
     *  positive integer k. It is used to prove that v3 is correct without
     *  having to do too much work.
     */
    function computeRootPathDiffUpv2(p : seq<bit>, h: nat, k : nat, b : seq<int>, seed: int) : int
        requires h == |p| == |b|
        requires |p| >= 1
        requires k < power2(|p|)
        requires natToBitList(k, |p|) == p
        ensures computeRootPathDiffUpv2(p, h, k, b, seed) == computeRootPathDiffUp(p, b, seed)
        decreases p
    {
     if |p| == 1 then
        if first(p) == 0 then diff(seed, 0)  else diff(last(b), seed)
    else 
        if last(p) == 0 then
            assert( k % 2 == 0);
            assert( h == |p|);
            computeRootPathDiffUpv2(init(p), h - 1, k / 2, init(b),diff(seed, 0))
        else        
            assert( k % 2 == 1);
            assert( h == |p|);
            computeRootPathDiffUpv2(init(p), h - 1, k / 2, init(b),diff(last(b), seed))
    }

    /**
     *  Compute root value using the integer vaklue of a path.
     */
    function method computeRootPathDiffUpv3(h: nat, k : nat, b : seq<int>, seed: int) : int
        requires h == |b|
        requires k < power2(h)
        ensures  h >= 1 ==> 
            computeRootPathDiffUpv3(h, k, b, seed) 
                ==  var p := natToBitList(k, h);
                    computeRootPathDiffUpv2(p, h, k, b, seed) 
        decreases h
    {
    if h == 0 then
        seed
    else 
        if k % 2 == 0 then
            computeRootPathDiffUpv3(h - 1, k / 2, init(b),diff(seed, 0))
        else        
            computeRootPathDiffUpv3(h - 1, k / 2, init(b),diff(last(b), seed))
    }

    lemma v3computesRootPath(h: nat, k : nat, b : seq<int>, seed: int) 
        requires 1 <= h == |b|
        requires k < power2(h)
        ensures computeRootPathDiffUpv3(h, k, b, seed) == 
            var p := natToBitList(k, h); computeRootPathDiffUpv2(p, h, k, b, seed) 
        ensures computeRootPathDiffUpv3(h, k, b, seed) == 
            var p := natToBitList(k, h); computeRootPathDiffUp(p, b, seed) 
    {
        //  Thanks Dafny
    }


    /**
     *  Collect all the diff values computed on the path p.
     */
    function computeAllPathDiffUp(p : seq<bit>, b : seq<int>, seed: int) : seq<int>
        requires |p| == |b|
        ensures |computeAllPathDiffUp(p, b, seed)| == |p| 
        decreases p
    {
     if |p| == 0 then
        [] 
    else 
        if last(p) == 0 then
            computeAllPathDiffUp(init(p), init(b), diff(seed, 0)) + [seed]
        else        
            computeAllPathDiffUp(init(p), init(b), diff(last(b), seed)) + [seed]
    }

    /**
     *  The sequence collected by computeAllPathDiffUp corresponds to the sequence
     *  of values computed by computeRootPathDiffUp on suffixes.
     */
    lemma computeAllDiffUpPrefixes(p : seq<bit>, b : seq<int>, seed: int)
        requires |p| == |b|
        ensures forall i :: 0 <= i < |computeAllPathDiffUp(p, b, seed)| ==>
            computeAllPathDiffUp(p, b, seed)[i] == computeRootPathDiffUp(drop(p, i + 1), drop(b, i + 1), seed) 
    {
        if |p| == 0 {
            //  Thanks Dafny.
        } else {
            forall ( i : nat | 0 <= i < |p|)
                ensures computeAllPathDiffUp(p, b, seed)[i] == computeRootPathDiffUp(drop(p, i + 1), drop(b, i + 1), seed) 
            {
                if last(p) == 0 {
                    if i < |p| - 1 {
                        calc == {
                            computeRootPathDiffUp(p, b, seed);
                            computeRootPathDiffUp(init(p), init(b), diff(seed, 0));
                        }
                        var a := computeAllPathDiffUp(init(p), init(b), diff(seed, 0)) + [diff(seed, 0)];
                        calc == {
                            computeAllPathDiffUp(p, b, seed)[i];
                            a[i];
                            { computeAllDiffUpPrefixes(init(p), init(b), diff(seed, 0)); }
                            computeRootPathDiffUp(drop(init(p), i + 1), drop(init(b), i + 1), diff(seed, 0)); 
                            calc == {   //  i + 1 < |p|
                                init(drop(p, i + 1)) ; 
                                { seqIndexLemmas(p, i + 1) ; }
                                drop(init(p),i + 1);
                            }   
                            computeRootPathDiffUp(init(drop(p, i + 1)), init(b)[ i + 1..], diff(seed, 0));
                            calc == { //  i + 1 < |p|
                                init(drop(b, i + 1));
                                { seqIndexLemmas(b, i + 1) ; }
                                drop(init(b), i + 1);
                            }  
                            computeRootPathDiffUp(init(drop(p, i + 1)), init(drop(b, i + 1)), diff(seed, 0));
                            //  Definition of computeRootPathDiffUp with last(p) == 0
                            computeRootPathDiffUp(drop(p, i + 1), drop(b, i + 1), seed) ;
                        }
                    } else {
                        //   i == |p| - 1
                    }
                } else {
                    //  last(p) == 1, same as last(p) == 0 except that diff(seed, 0) is
                    //  replaced by diff(last(b), seed)
                    if i < |p| - 1 {
                        calc == {
                            computeRootPathDiffUp(p, b, seed);
                            computeRootPathDiffUp(init(p), init(b), diff(last(b), seed));
                        }
                        var a := computeAllPathDiffUp(init(p), init(b), diff(last(b), seed)) + [diff(last(b), seed)];
                        calc == {
                            computeAllPathDiffUp(p, b, seed)[i];
                            a[i];
                            { computeAllDiffUpPrefixes(init(p), init(b), diff(last(b), seed)); }
                            computeRootPathDiffUp(drop(init(p), i + 1), drop(init(b), i + 1), diff(last(b), seed)); 
                            calc == {   //  i + 1 < |p|
                                init(drop(p, i + 1)) ; 
                                { seqIndexLemmas(p, i + 1) ; }
                                drop(init(p), i + 1);
                            }    
                            computeRootPathDiffUp(init(drop(p, i + 1)), drop(init(b), i + 1), diff(last(b), seed));
                           calc == { //  i + 1 < |p|
                                init(drop(b, i + 1));
                                { seqIndexLemmas(b, i + 1) ; }
                                drop(init(b), i + 1);
                            }   
                            computeRootPathDiffUp(init(drop(p, i + 1)), init(drop(b, i + 1)) ,diff(last(b), seed));
                            //  definition of computeRootPathDiffUp for last(p) == 1
                            computeRootPathDiffUp(drop(p, i + 1), drop(b, i + 1), seed) ;
                        }
                    } else {
                        //   i == |p| - 1
                    }
                }
            }
        }
    }

    /**
     *  Computing up or down yield the same result!
     */
    lemma {:induction p, b, seed} computeUpEqualsComputeDown(p : seq<bit>, b : seq<int>, seed: int) 
        requires |p| == |b|
        ensures computeRootPathDiffUp(p, b, seed) == computeRootPathDiff(p, b, seed)
    {
        if |p| <= 1 {
            //  Thanks Dafny
        } else {    
            //  |p| >= 2
            //  Split on values of last(p) 
            if last(p) == 0 {
                calc == {
                    computeRootPathDiffUp(p, b, seed);
                    computeRootPathDiffUp(init(p), init(b), diff(seed, 0));
                    //  Induction assumption
                    computeRootPathDiff(init(p), init(b), diff(seed, 0));
                    { simplifyComputeRootPathDiffOnLast(p, b, seed); }
                    computeRootPathDiff(p, b, seed);
                }
            } else  {
                assert(last(p) == 1 );
                calc == {
                    computeRootPathDiffUp(p, b, seed);
                     computeRootPathDiffUp(init(p), init(b), diff(last(b), seed));
                    //  Induction assumption
                    computeRootPathDiff(init(p), init(b),  diff(last(b), seed));
                    { simplifyComputeRootPathDiffOnLast(p, b, seed); }
                    computeRootPathDiff(p, b, seed);
                }
            }
        }
    }

    /**
     *  Show that if right sibling values are zero,  computeRootPathDiff
     *  computes the same result as computeRootPath.
     */
    lemma {:induction p} computeRootPathDiffEqualscomputeRootPath(p : seq<bit>, b : seq<int>, seed: int) 
        requires |b| == |p| 
        requires forall i :: 0 <= i < |b| ==> p[i] == 0 ==> b[i] == 0
        ensures computeRootPathDiff(p, b, seed) == computeRootPath(p, b, diff, seed)
        decreases p
    {
        if |p| == 0 {
            //  Thanks Dafny
        } else {
            //  Compute result on suffixes tail(p), tail(b)
            var r := computeRootPathDiff(tail(p), tail(b), seed);
            var r' := computeRootPath(tail(p), tail(b), diff, seed);

            //  Use inductive assumption on tail(p), tail(b) which implies r == r'
            calc == {
                r;
                { computeRootPathDiffEqualscomputeRootPath(tail(p), tail(b), seed); }
                r';
            }
            //  Finalise proof
            calc == {   //  These terms are equal
                computeRootPathDiff(p, b, seed) ;
                if first(p) == 0 then diff(r, 0) else  diff(first(b), r);
                if first(p) == 0 then diff(r', 0) else  diff(first(b), r');
                computeRootPath(p, b, diff, seed);
            }
        }
    }

    /**
     *  When two vectors b and b' have the same values for i such that p[i] == 1,
     *  i.e. for every left sibling b and b' coincide, then 
     *  computeRootPathDiff(p, b, seed) == computeRootPathDiff(p, b', seed)
     */
    lemma {:induction p} sameComputeDiffPath(p : seq<bit>, b : seq<int>, b': seq<int>, seed: int)
        requires |b| == |p| == |b'|
        requires forall i :: 0 <= i < |b| ==> p[i] == 1 ==> b[i] == b'[i]
        ensures computeRootPathDiff(p, b, seed) == computeRootPathDiff(p, b', seed)
        decreases p 
    {
        if |p| == 0 {
            //
        } else {
            var r := computeRootPathDiff(tail(p), tail(b), seed);
            var r' := computeRootPathDiff(tail(p), tail(b'), seed);
            //  Use inductive assumption on tail(p), tail(b) which implies r == r'
            calc == {
                r;
                { sameComputeDiffPath(tail(p), tail(b), tail(b'), seed); }
                r';
            }
            //  Finalise proof
            calc == {   //  These terms are equal
                computeRootPathDiff(p, b, seed) ;
                if first(p) == 0 then diff(r, 0) else  diff(first(b), r);
                if first(p) == 0 then diff(r', 0) else  diff(first(b), r');
                computeRootPathDiff(p, b', seed);
            }
        }
    }

    function makeB(p: seq<bit>, b: seq<int>) : seq<int> 
        requires |p| == |b|
        decreases p
        ensures |makeB(p, b)| == |b| && forall i :: 0 <= i < |b| ==> if p[i] == 1 then makeB(p,b)[i] == b[i] else makeB(p, b)[i] == 0 
    {
        if |p| == 0 then
            []
        else    
            [if first(p) == 0 then 0 else first(b)] + makeB(tail(p), tail(b))
    }

    /**
     *  Weakening of computeOnPathYieldsRootValue, requesting values on left siblings only, when
     *  merkle tree and path is not last non-null leaf.
     */
     lemma {:induction p, r, b} computeOnPathYieldsRootValueDiff(p : seq<bit>, r : Tree<int>, b : seq<int>, k : nat) 

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
        requires forall i :: 0 <= i < |b| ==> p[i] == 1 ==> b[i] == siblingAt(take(p, i + 1), r).v

        ensures r.v == computeRootPathDiff(p, b, leavesIn(r)[k].v)

        decreases r
    {

        //  define a new seq b' that holds default values for right siblings
        //  and prove that pre-conditions of computeOnPathYieldsRootValue hold.
        var b' := makeB(p, b);

        leavesRightOfNodeAtPathZeroImpliesRightSiblingsOnPathZero(r, k, p, 0);
        assert(forall i :: 0 <= i < |p| ==> 
            p[i] == 0 ==> siblingAt(take(p, i + 1), r).v == 0);

        siblingsLeft(p, r, b, b', k, 0);
        assert(forall i :: 0 <= i < |p| ==> b'[i] == siblingAt(take(p, i + 1), r).v);

        assert(forall i :: 0 <= i < |p| ==> p[i] == 0 ==> b'[i] == 0);

        computeOnPathYieldsRootValue(p, r, b', diff, leavesIn(r)[k].v);
        assert(computeRootPath(p, b', diff, leavesIn(r)[k].v) ==  r.v);
        computeRootPathDiffEqualscomputeRootPath(p, b', leavesIn(r)[k].v);
        assert(computeRootPathDiff(p, b',  leavesIn(r)[k].v) == computeRootPath(p, b', diff,  leavesIn(r)[k].v));

        sameComputeDiffPath(p, b, b', leavesIn(r)[k].v);
    }

    lemma {:induction p, r, b} computeOnPathYieldsRootValueDiff2(p : seq<bit>, r : Tree<int>, b : seq<int>, k : nat, index : nat) 

         requires isCompleteTree(r)
        /** `r` is decorated with attribute `f`. */
        requires isDecoratedWith(diff, r)
        requires height(r) >= 2

        /**  all leaves after the k leaf are zero. */
        requires k < |leavesIn(r)|
        requires forall i :: k < i < |leavesIn(r)| ==> leavesIn(r)[i].v == 0

        /** p is the path to k leaf in r. */
        requires hasLeavesIndexedFrom(r, index)
        requires |p| == height(r) - 1
        requires nodeAt(p, r) == leavesIn(r)[k]

        requires |b| == |p|
        /** `b` contains values at left siblings on path `p`. */
        requires forall i :: 0 <= i < |b| ==> p[i] == 1 ==> b[i] == siblingAt(take(p, i + 1), r).v

        ensures r.v == computeRootPathDiff(p, b, leavesIn(r)[k].v)

        decreases r
    {

        //  define a new seq b' that holds default values for right siblings
        //  and prove that pre-conditions of computeOnPathYieldsRootValue hold.
        var b' := makeB(p, b);

        leavesRightOfNodeAtPathZeroImpliesRightSiblingsOnPathZero(r, k, p, index);
        assert(forall i :: 0 <= i < |p| ==> 
            p[i] == 0 ==> siblingAt(take(p, i + 1), r).v == 0);

        siblingsLeft(p, r, b, b', k, index);
        assert(forall i :: 0 <= i < |p| ==> b'[i] == siblingAt(take(p, i + 1), r).v);

        assert(forall i :: 0 <= i < |p| ==> p[i] == 0 ==> b'[i] == 0);

        computeOnPathYieldsRootValue(p, r, b', diff, leavesIn(r)[k].v);
        assert(computeRootPath(p, b', diff, leavesIn(r)[k].v) ==  r.v);
        computeRootPathDiffEqualscomputeRootPath(p, b', leavesIn(r)[k].v);
        assert(computeRootPathDiff(p, b',  leavesIn(r)[k].v) == computeRootPath(p, b', diff,  leavesIn(r)[k].v));

        sameComputeDiffPath(p, b, b', leavesIn(r)[k].v);
    }

    /**
     *  Main function to compute the root value.
     */
     function computeRootDiffUp(p : seq<bit>, r : Tree<int>, b : seq<int>, k : nat) : int
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
        requires forall i :: 0 <= i < |b| ==> p[i] == 1 ==> b[i] == siblingAt(take(p, i + 1), r).v

        ensures r.v == computeRootDiffUp(p, r, b, k)
    {
        //  Values on left sibling are enough to compuute r.v using computeRootPathDiff
        computeOnPathYieldsRootValueDiff(p, r, b, k);
        //  Compute computeRootUp yields same value as computeRootPathDiff
        computeUpEqualsComputeDown(p, b, leavesIn(r)[k].v);
        computeRootPathDiffUp(p, b, leavesIn(r)[k].v)
    }

    /**
     *  A useful lemma need in the proof of v1Equalsv2 when |p| > 1 and last(p) == 1.
     *  
     *  It states that the values on  init(valOnPAt) (valOnPAt minus last element) must
     *  coincide with computations of prefixes of init(p) starting from a seed that 
     *  is the result of the computation of diff using the last values (node and it sibling).
     *
     *  @note   A tedious proof with lots of indices but not hard.
     */
    lemma prefixOfComputation(p : seq<bit>, valOnLeftAt : seq<int>, seed: int, valOnPAt: seq<int>) 
        requires |p| == |valOnLeftAt| ==  |valOnPAt|
        requires |p| >= 2
        requires forall i :: 0 <= i < |valOnPAt| ==> valOnPAt[i] == computeRootPathDiffUp(drop(p, i + 1), drop(valOnLeftAt, i + 1), seed) 
        ensures last(p) == 1 ==> forall i :: 0 <= i < |init(valOnLeftAt)| ==> 
                    init(valOnPAt)[i] == computeRootPathDiffUp(drop(init(p), i + 1), drop(init(valOnLeftAt), i + 1), diff(last(valOnLeftAt), seed)) 
    {
        if last(p) == 1 {
            forall (i : nat  | 0 <= i < |init(valOnPAt)|)
                    ensures init(valOnPAt)[i] == 
                        computeRootPathDiffUp( 
                            drop(init(p), i + 1), 
                            drop(init(valOnLeftAt), i + 1), 
                            diff(last(valOnLeftAt), seed)
                        ) 
            {
                //  drop does not changes last element
                calc == {
                    last(drop(p, i + 1));
                    { seqIndexLemmas(p, i + 1) ; }
                    last(p);
                    1;
                }
                //  as i < |init(valOnPAt)|, valOnPAt and init(valOnPAt) coincide
                calc == {
                    valOnPAt[i];
                    { seqIndexLemmas(valOnPAt, i) ; }
                    init(valOnPAt)[i];
                }
                calc == {
                    computeRootPathDiffUp(
                        drop(init(p), i + 1), 
                        drop(init(valOnLeftAt), i + 1),
                        diff(last(valOnLeftAt), seed) );
                    { seqIndexLemmas(valOnLeftAt, i + 1);  seqIndexLemmas(p, i + 1);  }
                    computeRootPathDiffUp(
                                init(drop(p, i + 1)), 
                                init(drop(valOnLeftAt, i + 1)),
                                diff(last(valOnLeftAt), seed)) ;
                    //  definition of computeRootPathDiffUp with last(drop(p, i + 1)) == 1
                    computeRootPathDiffUp(drop(p, i + 1), drop(valOnLeftAt, i + 1),  diff(last(valOnLeftAt), diff(last(valOnLeftAt), seed))); 
                    //  use requires
                    valOnPAt[i];
                    //  which is same s init(valOnPAt)[i]
                }
            }
        }
    }

    /**
     *  This is the most tedious lemma to prove.
     *  Some simplifications may be welcome at some point.
     *  The verification time is also large and a timeout may occur (see it to a valeu >= 60sec).
     */
    lemma computeAllPathDiffUpInATree(p : seq<bit>, r : Tree<int>, b : seq<int>, k : nat, seed: int, index : nat) 
        requires isCompleteTree(r)
        /** `r` is decorated with attribute `f`. */
        requires isDecoratedWith(diff, r)
        requires height(r) >= 2

        /**  all leaves after the k leaf are zero. */
        requires k < |leavesIn(r)|
        requires forall i :: k < i < |leavesIn(r)| ==> leavesIn(r)[i].v == 0

        /** p is the path to k leaf in r. */
        requires hasLeavesIndexedFrom(r, index)
        requires |p| == height(r) - 1
        requires nodeAt(p, r) == leavesIn(r)[k]
        requires seed == nodeAt(p,r).v 

        requires |b| == |p|
        /** `b` contains values at left siblings on path `p`. */
        requires forall i :: 0 <= i < |b| ==> p[i] == 1 ==> b[i] == siblingAt(take(p, i + 1), r).v

        ensures forall i :: 0 <= i < |p| ==> 
            nodeAt(take(p, i + 1), r).v == computeAllPathDiffUp(p, b, seed)[i]
    {
        if |p| == 1 {
            //  Thanks Dafny.
        } else {
            //  |p| >= 2
            //  use induction to get i >=1 and computation on p[0] to get i == 0
            forall ( i : nat |  0 <= i < |p| )
                ensures nodeAt(take(p, i + 1), r).v == computeAllPathDiffUp(p, b, seed)[i]
            {
            match r 
                case Node(_, lc, rc) => 
                    var b':= makeB(p, b);

                    //  Collect true facts
                    calc ==> {
                        true;
                        isCompleteTree(r);
                        height(lc) == height(rc) == height(r) - 1 &&
                            isCompleteTree(lc) && isCompleteTree(rc);
                    }
                    calc ==> {
                        true;
                        { assert( isDecoratedWith(diff, r)) ; }
                        isDecoratedWith(diff, lc) && isDecoratedWith(diff, rc);
                    }
                    calc ==> {
                        true;
                        { childrenCompTreeValidIndex(r, height(r), index); }
                        hasLeavesIndexedFrom(lc, index) 
                            && hasLeavesIndexedFrom(rc, index + power2(height(r) - 1)/ 2);
                    }
                    calc ==> {
                        true;
                        { childrenInCompTreesHaveHalfNumberOfLeaves(r, height(r)); }
                        leavesIn(lc) == leavesIn(r)[.. power2(height(r) - 1) / 2]
                            && leavesIn(rc) == leavesIn(r)[power2(height(r) - 1) / 2 ..];
                    }
                    calc ==> {
                        true;
                        { completeTreeNumberLemmas(r); }
                         k < |leavesIn(r)| == power2(height(r) - 1);
                    }
                    calc ==> {
                        true;
                        { assert(forall i :: 0 <= i < |b| ==> p[i] == 1 ==> b[i] == siblingAt(take(p, i + 1), r).v) ;}
                        forall i :: 0 <= i < |b| ==> p[i] == 1 ==> b[i] == siblingAt(take(p, i + 1), r).v;
                        { siblingsLeft(p, r, b, b', k, index); }
                        forall i :: 0 <= i < |b'| ==> b'[i] == siblingAt(take(p, i + 1), r).v;
                    }
                    calc ==> {
                        true;
                        { assert(forall i :: 0 <= i < |b| ==> p[i] == 1 ==> b[i] == siblingAt(take(p, i + 1), r).v) ;}
                        forall i :: 0 <= i < |b| ==> p[i] == 1 ==> b[i] == siblingAt(take(p, i + 1), r).v;
                        { projectValuesOnChild(p, r, b'); }
                        forall k :: 0 <= k < |tail(b')|  ==>
                            tail(b')[k] == siblingAt(take(tail(p), k + 1), if first(p) == 0 then lc else rc).v;
                    }

                    if ( i >= 1 ) {
                        if first(p) == 0 {
                            calc ==> {
                                first(p) == 0;
                                { initPathDeterminesIndex(r, p, k, index); }
                                 k < power2(height(r) - 1)/ 2;
                            }
                            calc == {
                                nodeAt(take(p, i + 1), r).v;
                                { 
                                    foo777(p, r, i); 
                                }
                                nodeAt(take(tail(p), i), lc).v;
                                { computeAllPathDiffUpInATree(tail(p), lc, tail(b'), k, seed, index); }
                                computeAllPathDiffUp(tail(p), tail(b'), seed)[i - 1];
                                { computeAllDiffUpPrefixes(tail(p), tail(b'), seed); }
                                computeRootPathDiffUp(drop(p, i + 1), drop(b', i + 1), seed);
                                { computeUpEqualsComputeDown(drop(p, i + 1), drop(b', i + 1), seed); }
                                computeRootPathDiff(drop(p, i + 1), drop(b', i + 1), seed);
                                { sameComputeDiffPath(drop(p, i + 1), drop(b', i + 1), drop(b, i + 1), seed); 
                                }
                                computeRootPathDiff(drop(p, i + 1), drop(b, i + 1), seed);
                                { computeUpEqualsComputeDown(drop(p, i + 1), drop(b, i + 1), seed); 
                                }
                                computeRootPathDiffUp(drop(p, i + 1), drop(b, i + 1), seed);
                                { computeAllDiffUpPrefixes(p, b, seed); }
                                computeAllPathDiffUp(p, b, seed)[i];
                            }
                        } else {
                            initPathDeterminesIndex(r, p, k, index);
                            assert(k  >= power2(height(r) - 1)/ 2);
                            var k' := k - power2(height(r) - 1)/ 2;
                            var index' := index + power2(height(r) - 1)/ 2;
                            calc == {
                                nodeAt(take(p, i + 1), r).v;
                                { 
                                    foo777(p, r, i); 
                                }
                                nodeAt(take(tail(p), i), rc).v;
                                { computeAllPathDiffUpInATree(tail(p), rc, tail(b'), k', seed, index'); }
                                computeAllPathDiffUp(tail(p), tail(b'), seed)[i - 1];
                                { computeAllDiffUpPrefixes(tail(p), tail(b'), seed); }
                                computeRootPathDiffUp(drop(p, i + 1), drop(b', i + 1), seed);
                                { computeUpEqualsComputeDown(drop(p, i + 1), drop(b', i + 1), seed); }
                                computeRootPathDiff(drop(p, i + 1), drop(b', i + 1), seed);
                                { sameComputeDiffPath(drop(p, i + 1), drop(b', i + 1), drop(b, i + 1), seed); 
                                }
                                computeRootPathDiff(drop(p, i + 1), drop(b, i + 1), seed);
                                { computeUpEqualsComputeDown(drop(p, i + 1), drop(b, i + 1), seed); 
                                }
                                computeRootPathDiffUp(drop(p, i + 1), drop(b, i + 1), seed);
                                { computeAllDiffUpPrefixes(p, b, seed); }
                                computeAllPathDiffUp(p, b, seed)[i];
                            }
                        }
                    } else {
                        //  i == 0
                        if first(p) == 0 {
                            calc ==> {
                                first(p) == 0;
                                { initPathDeterminesIndex(r, p, k, index); }
                                 k < power2(height(r) - 1)/ 2;
                            }
                            calc == {
                                computeAllPathDiffUp(p, b, seed)[0];
                                { computeAllDiffUpPrefixes(p, b, seed); }
                                computeRootPathDiffUp(tail(p), tail(b),seed) ;
                                { computeUpEqualsComputeDown(tail(p), tail(b), seed); }
                                computeRootPathDiff(tail(p), tail(b),seed) ;
                                { sameComputeDiffPath(tail(p), tail(b'), tail(b), seed); }
                                computeRootPathDiff(tail(p), tail(b'), seed);
                                { computeOnPathYieldsRootValueDiff2(tail(p), lc, tail(b'), k, index); }
                                lc.v;
                                nodeAt(take(p, 0 + 1), r).v;
                            }
                        } else {
                           calc ==> {
                                first(p) == 0;
                                { initPathDeterminesIndex(r, p, k, index); }
                                k >= power2(height(r) - 1)/ 2;
                            }
                            var k' := k - power2(height(r) - 1)/ 2;
                            var index':= index + power2(height(r) - 1)/ 2;
                            calc == {
                                computeAllPathDiffUp(p, b, seed)[0];
                                { computeAllDiffUpPrefixes(p, b, seed); }
                                computeRootPathDiffUp(tail(p), tail(b),seed) ;
                                { computeUpEqualsComputeDown(tail(p), tail(b), seed); }
                                computeRootPathDiff(tail(p), tail(b),seed) ;
                                { sameComputeDiffPath(tail(p), tail(b'), tail(b), seed); }
                                computeRootPathDiff(tail(p), tail(b'), seed);
                                { computeOnPathYieldsRootValueDiff2(tail(p), rc, tail(b'), k', index'); }
                                rc.v;
                                nodeAt(take(p, 0 + 1), r).v;
                            }
                        }
                    }
            }
        }
    }
 }