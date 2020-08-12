 include "./Trees2.dfy"
 include "./Helpers.dfy"
 include "./IntTree.dfy"
include "MerkleTrees.dfy"
include "SeqOfBits.dfy"
include "CompleteTrees.dfy"
include "PathInCompleteTrees.dfy"
include "SeqHelpers.dfy"



 module Foo {
 
    import opened Trees
    import opened Helpers
    import opened DiffTree
    import opened MerkleTrees
    import opened SeqOfBits
    import opened CompleteTrees
    import opened PathInCompleteTrees
    import opened SeqHelpers

    /**
     *  Compute the value of attribute `f` on a path.
     *  
     *  @param  p       A path.
     *  @param  b       The value of `f` on each sibling after path[..k + 1]
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
            var r := computeRootPath(p[1..], b[1..], f, seed);
            if p[0] == 0 then
                f(r, b[0])
            else 
                f(b[0], r)
    }

    /**
     *  Relate values on siblings of child to suffix of b.
     */
    lemma {:induction r} restrictValuesOnChild<T>(p : seq<bit>, r : Tree<T>, b : seq<T>)  
        requires 1 <= |p| < height(r) 
        requires isCompleteTree(r)
        requires |b| == |p|
        requires forall k :: 0 <= k < |b| ==> b[k] == siblingAt(p[..k + 1], r).v
        /** Depending on p[0], `b` projects onto `lc or `rc`. */
        ensures match r
            case Node(_, lc, rc) =>
                forall k :: 0 <= k < |b| - 1 ==>
                if p[0] == 0 then
                    b[1..][k] == siblingAt(p[1..][..k + 1], lc).v
                else 
                    b[1..][k] == siblingAt(p[1..][..k + 1], rc).v
    {
        match r 
            case Node(_, lc, rc)=> 
                forall (k : nat | 0 <= k < |b| - 1) 
                    ensures 
                        0 <= k < |b| - 1 ==> 
                            if p[0] == 0 then
                                b[1..][k] == siblingAt(p[1..][..k + 1], lc).v
                            else 
                                b[1..][k] == siblingAt(p[1..][..k + 1], rc).v   
                {
                    //  Select child to use in induction according to p[0]
                    if ( k == 0 ) {
                        assume(if p[0] == 0 then
                                b[1..][0] == siblingAt(p[1..][..0 + 1], lc).v
                            else 
                                b[1..][0] == siblingAt(p[1..][..0 + 1], rc).v   );
                    } else {
                        assert( k >= 1 );
                        var child := if p[0] == 0 then lc else rc ;
                        calc == {   //  These terms are equal
                            b[1..][k] ;
                            b[k + 1];
                            siblingAt(p[..k + 1 + 1], r).v;
                            { foo119(p[..k + 1 + 1], r) ; }
                            siblingAt(p[..k + 1 + 1][1..], child).v;
                            //  Next step holds because of this equality:
                            calc == {
                                p[..k + 1 + 1][1..];
                                p[1..][..k + 1];
                            }
                            siblingAt(p[1..][..k + 1], child).v;
                            // (if p[0] == 0 then
                            //     b[1..][k] == siblingAt(p[1..][..k + 1], lc).v
                            // else 
                            //     b[1..][k] == siblingAt(p[1..][..k + 1], rc).v)  ;
                        }
                        // assume(if p[0] == 0 then
                        //         b[1..][0] == siblingAt(p[1..][..0 + 1], lc).v
                        //     else 
                        //         b[1..][0] == siblingAt(p[1..][..0 + 1], rc).v   );
                    }
                }
    }

    /**
     *  The value computed by computeRootPath is the same as the value of the root
     *  of the tree.
     *
     *  @param  p       A path.
     *  @param  r       A tree.
     *  @param  b       The value of `f` on siblings on path `p`.
     *  @param  f       A binary operation.
     *  @param  seed    A value.
     */
    lemma {:induction p, r, b} computeOnPathYieldsRootValue<T>(p : seq<bit>, r : Tree<T>, b : seq<T>, f : (T,T) -> T, seed: T) 
        requires 1 <= |p| == height(r) - 1
        requires isCompleteTree(r)
        /** `r` is deccorated with attribute `f`. */
        requires isDecoratedWith(f, r)
        /** Seed is the value at the leaf of the path `p`. */
        requires seed == nodeAt(p, r).v
        requires |b| == |p|
        /** `b` contains values at siblings on path `p`. */
        requires forall i :: 0 <= i < |b| ==> b[i] == siblingAt(p[..i + 1], r).v

        ensures r.v == computeRootPath(p, b, f, seed)

        decreases p
    {
        if |p| <= 1 {
            //  Thanks Dafny
        } else {  
            restrictValuesOnChild(p, r, b);
            
            match r
                case Node(_, lc, rc) =>

                // cby definition r.v == f(lc.v, rc.v)
                //  We show that whatever child is on path `p`  we have 
                //  the value of the sibling.

                var child := if p[0] == 0 then lc else rc ;
                var a := if p[0] == 0 then 1 else 0;

                //  Induction on lc or rc depending on p[0]
                computeOnPathYieldsRootValue(p[1..], child, b[1..], f, seed);
                // this implies that if p[0] == 0 then lc.v else rc.v == 
                //                           computeRootPath(p[1..], b[1..], f, seed))

                calc == {
                    b[0] ;
                    nodeAt([] + [a], r).v;
                    calc {  //  simplify
                        [] + [a];
                        [a];
                    }
                    nodeAt([a], r).v;
                    (if p[0] == 0 then rc.v else lc.v);
                }
        }
    }

    /**
     *  If b and b' agree on values at which p[i] == 1 and b has siblings at p[..], then 
     *  b' has siblings at same location.  
     */
    lemma siblingsLeft(p : seq<bit>, l : seq<int>, r : Tree<int>, b : seq<int>, b': seq<int>, k : nat) 
        /** Merkle tree. */
        requires height(r) >= 2
        requires |l| == |leavesIn(r)|
        requires isMerkle2(r, l, diff)

        /**  all leaves after the k leaf are zero. */
        requires k < |leavesIn(r)|
        requires forall i :: k < i < |l| ==> l[i] == 0

        /** p is the path to k leaf in r. */
        requires |p| == height(r) - 1
        requires nodeAt(p, r) == leavesIn(r)[k]

        requires |b| == |p|
        /** `b` contains values at left siblings on path `p`. */
        requires forall i :: 0 <= i < |b| ==> p[i] == 1 ==> b[i] == siblingAt(p[..i + 1], r).v

        requires |b'| == |b| && forall i :: 0 <= i < |b'| ==> if p[i] == 1 then b'[i] == b[i] else b'[i] == 0 

        ensures forall i :: 0 <= i < |b'| ==> b'[i] == siblingAt(p[..i + 1], r).v
    {
        t2(r, l, k, p);
        
    }

    /**
     *  Same as computeRootPath but uses default value 0 on 
     *  right sibling to compute value at root.
     *  Compute the value on a path by computing on child first.
     */
    function computeRootPathDiff(p : seq<bit>, b : seq<int>, seed: int) : int
        requires |p| == |b|
        decreases p
    {
        if |p| == 0 then 
            seed
        else 
            var r := computeRootPathDiff(p[1..], b[1..], seed);
            if p[0] == 0 then
                diff(r, 0)
            else 
                diff(b[0], r)
    }

    /**
     *  Compute computeRootPathDiff by pre-computing the last 
     *  step.
     */
    lemma {:induction p, b} foo506(p : seq<bit>, b : seq<int>, seed: int) 
        requires 1 <= |p| == |b|
        ensures computeRootPathDiff(p, b, seed) == 
            computeRootPathDiff(
                p[..|p| - 1], b[..|b| - 1], 
                if p[|p| - 1] == 0 then 
                    diff(seed, 0)
                else 
                    diff(b[|b| - 1], seed)
                )
    {
        if |p| == 1 {
            // Thanks Dafny
        } else {
            if p[0] == 0 {
                calc == {
                    computeRootPathDiff(p, b, seed);
                    diff(computeRootPathDiff(p[1..], b[1..], seed), 0);
                    diff(
                        computeRootPathDiff(p[1..][..|p[1..]| - 1], b[1..][..|b[1..]| - 1], 
                        if p[1..][|p[1..]| - 1] == 0 then diff(seed, 0)
                        else diff(b[1..][|b[1..]| - 1], seed)
                        ), 0
                    );
                    calc == {
                        p[1..][..|p[1..]| - 1];
                        p[1..|p| - 1];
                    }
                    diff(
                        computeRootPathDiff(p[1..|p| - 1], b[1..][..|b[1..]| - 1], 
                        if p[|p| - 1] == 0 then diff(seed, 0)
                        else diff(b[1..][|b[1..]| - 1], seed)
                        ), 0
                    );
                    calc == {
                        b[1..][..|b[1..]| - 1];
                        b[1..|b| - 1];
                    }
                    diff(
                        computeRootPathDiff(p[1..|p| - 1], b[1..|b| - 1], 
                        if p[|p| - 1] == 0 then diff(seed, 0)
                        else diff(b[|b| - 1], seed)
                        ), 0
                    );
                }
            }
            else {
                calc == {
                    computeRootPathDiff(p, b, seed);
                    diff(b[0], computeRootPathDiff(p[1..], b[1..], seed));
                    diff(
                        b[0],
                        computeRootPathDiff(p[1..][..|p[1..]| - 1], b[1..][..|b[1..]| - 1], 
                        if p[1..][|p[1..]| - 1] == 0 then diff(seed, 0)
                        else diff(b[1..][|b[1..]| - 1], seed)
                        )
                    );
                    calc == {
                        p[1..][..|p[1..]| - 1];
                        p[1..|p| - 1];
                    }
                    diff(
                        b[0],
                        computeRootPathDiff(p[1..|p| - 1], b[1..][..|b[1..]| - 1], 
                        if p[|p| - 1] == 0 then diff(seed, 0)
                        else diff(b[1..][|b[1..]| - 1], seed)
                        )
                    );
                    calc == {
                        b[1..][..|b[1..]| - 1];
                        b[1..|b| - 1];
                    }
                    diff(
                        b[0],
                        computeRootPathDiff(p[1..|p| - 1], b[1..|b| - 1], 
                        if p[|p| - 1] == 0 then diff(seed, 0)
                        else diff(b[|b| - 1], seed)
                        )
                    );
                }            
            }
        }
    }

    /**
     *  Compute root value starting from end of path.
     */
    function computeRootUp(p : seq<bit>, b : seq<int>, seed: int) : int
        requires |p| == |b|
        decreases p
    {
     if |p| == 0 then
        seed 
    else 
        if p[|p| - 1] == 0 then
            computeRootUp(p[.. |p| - 1], b[..|b| - 1],diff(seed, 0))
        else        
            computeRootUp(p[.. |p| - 1], b[..|b| - 1],diff(b[|b| - 1], seed))
    }

    
    lemma {:induction p, b, seed} foo510(p : seq<bit>, b : seq<int>, seed: int) 
        requires |p| == |b|
        ensures computeRootUp(p, b, seed) == computeRootPathDiff(p, b, seed)
    {
        if |p| <= 1 {
            //  Thanks Dafny
        } else {    
            //  |p| >= 2
            //  Split on values of p[|p| - 1]
            if p[|p| - 1] == 0 {
                calc == {
                    computeRootUp(p, b, seed);
                    computeRootUp(p[.. |p| - 1], b[..|b| - 1],diff(seed, 0));
                    //  Induction assumption
                    computeRootPathDiff(p[.. |p| - 1], b[..|b| - 1],diff(seed, 0));
                    { foo506(p, b, seed); }
                    computeRootPathDiff(p, b, seed);
                }
            } else  {
                assert(p[|p| - 1] == 1 );
                calc == {
                    computeRootUp(p, b, seed);
                     computeRootUp(p[.. |p| - 1], b[..|b| - 1],diff(b[|b| - 1], seed));
                    //  Induction assumption
                    computeRootPathDiff(p[.. |p| - 1], b[..|b| - 1], diff(b[|b| - 1], seed));
                    { foo506(p, b, seed); }
                    computeRootPathDiff(p, b, seed);
                }
            }
        }
    }

    /**
     *  Show that if right sibling values are zero,  computeRootPathDiff
     *  computes the same result as computeRootPath.
     */
    lemma {:induction p} foo304(p : seq<bit>, b : seq<int>, seed: int) 
        requires |b| == |p| 
        requires forall i :: 0 <= i < |b| ==> p[i] == 0 ==> b[i] == 0
        ensures computeRootPathDiff(p, b, seed) == computeRootPath(p, b, diff, seed)
        decreases p
    {
        if |p| == 0 {
            //  Thanks Dafny
        } else {
            //  Compute result on suffixes p[1..], b[1..]
            var r := computeRootPathDiff(p[1..], b[1..], seed);
            var r' := computeRootPath(p[1..], b[1..], diff, seed);

            //  Use inductive assumption on p[1..], b[1..]
            foo304(p[1..], b[1..], seed);
            // HI implies r == r'
            
            calc == {   //  These terms are equal
                computeRootPathDiff(p, b, seed) ;
                if p[0] == 0 then diff(r, 0) else  diff(b[0], r);
                if p[0] == 0 then diff(r', 0) else  diff(b[0], r');
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
            var r := computeRootPathDiff(p[1..], b[1..], seed);
            var r' := computeRootPathDiff(p[1..], b'[1..], seed);
            if p[0] == 0 {
                calc == {
                    computeRootPathDiff(p, b, seed) ;
                    diff(r, 0) ;
                    // Induction on p[1..], b[1..], b'[1..], seed
                    { sameComputeDiffPath(p[1..], b[1..], b'[1..], seed); }  
                    diff(r', 0);
                    computeRootPathDiff(p, b', seed);
                }
            } else {
                calc == {
                    computeRootPathDiff(p, b, seed) ;
                    diff(b[0], r) ;
                    // Induction on p[1..], b[1..], b'[1..], seed
                    { sameComputeDiffPath(p[1..], b[1..], b'[1..], seed); }  
                    diff(b'[0], r');
                    computeRootPathDiff(p, b', seed);
                }
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
            [if p[0] == 0 then 0 else b[0]] + makeB(p[1..], b[1..])
    }

    /**
     *  Weakening of computeOnPathYieldsRootValue, requesting values on left siblings only, when
     *  merkle tree and path is not last non-null leaf.
     */
     lemma {:induction p, r, b} computeOnPathYieldsRootValueDiff(p : seq<bit>, l : seq<int>, r : Tree<int>, b : seq<int>, k : nat) 
        /** Merkle tree. */
        requires height(r) >= 2
        requires |l| == |leavesIn(r)|
        requires isMerkle2(r, l, diff)

        /**  all leaves after the k leaf are zero. */
        requires k < |leavesIn(r)|
        requires forall i :: k < i < |l| ==> l[i] == 0

        /** p is the path to k leaf in r. */
        requires |p| == height(r) - 1
        requires nodeAt(p, r) == leavesIn(r)[k]

        requires |b| == |p|
        /** `b` contains values at left siblings on path `p`. */
        requires forall i :: 0 <= i < |b| ==> p[i] == 1 ==> b[i] == siblingAt(p[..i + 1], r).v

        ensures r.v == computeRootPathDiff(p, b, leavesIn(r)[k].v)

        decreases r
    {

        //  define a new seq b' that holds default values for right siblings
        //  and prove that pre-conditions of computeOnPathYieldsRootValue hold.

        // var b' : seq<int> :| |b'| == |b| && forall i :: 0 <= i < |b| ==> if p[i] == 1 then b'[i] == b[i] else b'[i] == 0 ; 
        var b' := makeB(p, b);

        t2(r, l, k, p);
        assert(forall i :: 0 <= i < |p| ==> 
            p[i] == 0 ==> siblingAt(p[..i + 1], r).v == 0);

        siblingsLeft(p, l, r, b, b', k);
        assert(forall i :: 0 <= i < |p| ==> b'[i] == siblingAt(p[..i + 1], r).v);

        assert(forall i :: 0 <= i < |p| ==> p[i] == 0 ==> b'[i] == 0);

        computeOnPathYieldsRootValue(p, r, b', diff, leavesIn(r)[k].v);
        assert(computeRootPath(p, b', diff, leavesIn(r)[k].v) ==  r.v);
        foo304(p, b', leavesIn(r)[k].v);
        assert(computeRootPathDiff(p, b',  leavesIn(r)[k].v) == computeRootPath(p, b', diff,  leavesIn(r)[k].v));

        sameComputeDiffPath(p, b, b', leavesIn(r)[k].v);
    }

    /**
     *  Main function to compute the root value.
     */
     function computeRootDiffUp(p : seq<bit>, l : seq<int>, r : Tree<int>, b : seq<int>, k : nat) : int
        /** Merkle tree. */
        requires height(r) >= 2
        requires |l| == |leavesIn(r)|
        requires isMerkle2(r, l, diff)

        /**  all leaves after the k leaf are zero. */
        requires k < |leavesIn(r)|
        requires forall i :: k < i < |l| ==> l[i] == 0

        /** p is the path to k leaf in r. */
        requires |p| == height(r) - 1
        requires nodeAt(p, r) == leavesIn(r)[k]

        requires |b| == |p|
        /** `b` contains values at left siblings on path `p`. */
        requires forall i :: 0 <= i < |b| ==> p[i] == 1 ==> b[i] == siblingAt(p[..i + 1], r).v

        ensures r.v == computeRootDiffUp(p, l, r, b, k)
    {
        //  Values on left sibling are enough to compuute r.v using computeRootPathDiff
        computeOnPathYieldsRootValueDiff(p, l, r, b, k);
        //  Compute computeRootUp yields same value as computeRootPathDiff
        foo510(p, b, leavesIn(r)[k].v);
        computeRootUp(p, b, leavesIn(r)[k].v)
    }

    /**
     *  The binary encoding of k of height(r) - 1 is the path leading to leaf k.
     */
    lemma {:induction r} foo111(r : Tree<int>, k : nat) 

        requires isCompleteTree(r)
        requires height(r) >= 2
        requires k < |leavesIn(r)|

        ensures k < power2(height(r) - 1) 
        ensures nodeAt(natToBitList(k, height(r) - 1), r) ==  leavesIn(r)[k]
    {
        completeTreeNumberLemmas(r);
        foo909(k, height(r) - 1);
        assert(bitListToNat(natToBitList(k, height(r) - 1)) == k);
        foo200(natToBitList(k, height(r) - 1), r, k);
    }

    function incMerkle(p: seq<bit>, l : seq<int>, r : Tree<int>, b : seq<int>, k : nat) : (int, seq<int>) 
        //  current leaf is not the last one
        requires height(r) >= 2
        requires  isCompleteTree(r)
        requires |l| == |leavesIn(r)|
        requires k < |leavesIn(r)| - 1
        requires forall i :: k < i < |l| ==> l[i] == 0

        requires k < power2(height(r) - 1) 
        requires |b| == |p|
        requires isMerkle2(r, l, diff)

        requires p == natToBitList(k, height(r) - 1)
        requires forall i :: 0 <= i < |b| ==> p[i] == 1 ==> b[i] == siblingAt(p[..i + 1], r).v

        ensures r.v == incMerkle(p, l, r, b, k).0
    {
        // var p := natToBitList(k, height(r) - 1);
        assert(|p| == height(r) - 1);
        foo111(r,k);
        // foo200(natToBitList(k, height(r) - 1), r, k);

        assert(nodeAt(p, r) == leavesIn(r)[k]);
        (computeRootDiffUp(p, l, r, b, k), [])
    }


 }