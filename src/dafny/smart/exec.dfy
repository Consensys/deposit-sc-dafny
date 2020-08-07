 include "./Trees2.dfy"
 include "./Helpers.dfy"
 include "./IntTree.dfy"
include "MerkleTrees.dfy"

 module Foo {
 
    import opened Trees
    import opened Helpers
    import opened DiffTree
    import opened MerkleTrees


    // function foo1<T>(p : seq<bit>, r : ITree<T>, b : seq<T>) : int 
    //     requires |p| == height(r) - 1
    //     requires isCompleteTree(r)
    //     requires |b| == |siblings(p, r)|
    // {
    //     0
    // }

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
    lemma {:induction r} restrictValuesOnChild<T>(p : seq<bit>, r : ITree<T>, b : seq<T>)  
        requires 1 <= |p| < height(r) 
        requires isCompleteTree(r)
        requires |b| == |p|
        requires forall k :: 0 <= k < |b| ==> b[k] == siblingAt(p[..k + 1], r).v
        /** Depending on p[0], `b` projects onto `lc or `rc`. */
        ensures match r
            case INode(_, lc, rc, _) =>
                forall k :: 0 <= k < |b| - 1 ==>
                if p[0] == 0 then
                    b[1..][k] == siblingAt(p[1..][..k + 1], lc).v
                else 
                    b[1..][k] == siblingAt(p[1..][..k + 1], rc).v
    {
        match r 
            case INode(_, lc, rc,_) => 
                forall (k : nat | 0 <= k < |b| - 1) 
                    ensures 
                        0 <= k < |b| - 1 ==> 
                            if p[0] == 0 then
                                b[1..][k] == siblingAt(p[1..][..k + 1], lc).v
                            else 
                                b[1..][k] == siblingAt(p[1..][..k + 1], rc).v   
                {
                    if p[0] == 0 {
                        calc == {
                            b[1..][k] ;
                            == 
                            b[k + 1];
                            ==
                            siblingAt(p[..k + 1 + 1], r).v;
                            ==
                            siblingAt(p[..k + 1 + 1][1..], lc).v;
                            == { prefixOfSuffixCommutes(p, k + 1); }
                            siblingAt(p[1..][..k + 1], lc).v;
                        }
                    } else {
                        calc == {
                            b[1..][k] ;
                            == 
                            b[k + 1];
                            ==
                            siblingAt(p[..k + 1 + 1], r).v;
                            ==
                            siblingAt(p[..k + 1 + 1][1..], rc).v;
                            == { prefixOfSuffixCommutes(p, k + 1); }
                            siblingAt(p[1..][..k + 1], rc).v;
                        }
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
    lemma {:induction p, r, b} computeOnPathYieldsRootValue<T>(p : seq<bit>, r : ITree<T>, b : seq<T>, f : (T,T) -> T, seed: T) 
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
        if |p| == 1 {
            //  Thanks Dafny
        } else {  
            restrictValuesOnChild(p, r, b);
        }   
    }

    lemma siblingsLeft(p : seq<bit>, l : seq<int>, r : ITree<int>, b : seq<int>, b': seq<int>, k : nat) 
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
        // forall ( i :: 0 <= i < |b'| )
        //     ensures b'[i] == siblingAt(p[..i + 1], r).v
        // {
        //     if p[i] == 
        // }
    }

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

    lemma {:induction p} foo304(p : seq<bit>, b : seq<int>, seed: int) 
        requires |b| == |p| 
        requires forall i :: 0 <= i < |b| ==> p[i] == 0 ==> b[i] == 0
        ensures computeRootPathDiff(p, b, seed) == computeRootPath(p, b, diff, seed)
    {
        if |p| == 0 {
            //
        } else {
            var r := computeRootPathDiff(p[1..], b[1..], seed);
            var r' := computeRootPath(p[1..], b[1..], diff, seed);
            foo304(p[1..], b[1..], seed);
            assert(r == r');
            // HI: r == r'
            
            if p[0] == 0 {
                calc {
                    computeRootPathDiff(p, b, seed) ;
                    ==
                    diff(r, 0);
                    == 
                    diff(r', 0);
                    == 
                    computeRootPath(p, b, diff, seed);
                }
            } else {
                //  p[0] == 1
                calc {
                    computeRootPathDiff(p, b, seed) ;
                    ==
                    diff(b[0], r);
                    == 
                    diff(b[0], r');
                    == 
                    computeRootPath(p, b, diff, seed);
                }
            }
        }
    }

    lemma {:induction p} sameComputeDiffPath(p : seq<bit>, b : seq<int>, b': seq<int>, seed: int)
        requires |b| == |p| == |b'|
        requires forall i :: 0 <= i < |b| ==> p[i] == 1 ==> b[i] == b'[i]
        ensures computeRootPathDiff(p, b, seed) == computeRootPathDiff(p, b', seed)
    {
        if |p| == 0 {
            //
        } else {
            var r := computeRootPathDiff(p[1..], b[1..], seed);
            var r' := computeRootPathDiff(p[1..], b'[1..], seed);
            if p[0] == 0 {
                //
                calc {
                    computeRootPathDiff(p, b, seed) ;
                    ==
                    diff(r, 0) ;
                    == { sameComputeDiffPath(p[1..], b[1..], b'[1..], seed); }  
                    diff(r', 0);
                    ==
                    computeRootPathDiff(p, b', seed);
                }
            } else {
                calc {
                    computeRootPathDiff(p, b, seed) ;
                    ==
                    diff(b[0], r) ;
                    == { sameComputeDiffPath(p[1..], b[1..], b'[1..], seed); }  
                    diff(b'[0], r');
                    == 
                    computeRootPathDiff(p, b', seed);
                }
            }
        }
    }

    /**
     *  Weakening of computeOnPathYieldsRootValue, requesting values on left siblings only, when
     *  merkle tree and path is not last non-null leaf.
     */
     lemma {:induction p, r, b} computeOnPathYieldsRootValueDiff(p : seq<bit>, l : seq<int>, r : ITree<int>, b : seq<int>, k : nat) 
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

        var b' : seq<int>;
        assume( |b'| == |b| && forall i :: 0 <= i < |b| ==> if p[i] == 1 then b'[i] == b[i] else b'[i] == 0 ); 

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
 }