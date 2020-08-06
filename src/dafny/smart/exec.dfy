 include "./Trees2.dfy"
 include "./Helpers.dfy"

 module Foo {
 
    import opened Trees
    import opened Helpers

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
 }