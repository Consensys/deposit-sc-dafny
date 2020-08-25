
include "CompleteTrees.dfy"
include "MerkleTrees.dfy"
include "PathInCompleteTrees.dfy"
include "SeqOfBits.dfy"
include "Trees2.dfy"

module GenericComputation {
 
    import opened CompleteTrees
    import opened MerkleTrees
    import opened PathInCompleteTrees
    import opened SeqOfBits
    import opened Trees

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

    //  Properties of computeRootPath

    /**
     *  If a seq of values b corresponds to the values of siblings on a path,
     *  then p[1..] corresponds to siblings of lc or rc depending on p[0].
     */
    lemma {:induction r} projectValuesOnChild<T>(p : seq<bit>, r : Tree<T>, b : seq<T>)  
        requires 1 <= |p| < height(r) 
        requires isCompleteTree(r)
        requires |b| == |p|
        requires forall k :: 0 <= k < |b| ==> b[k] == siblingAt(p[..k + 1], r).v
        /** Depending on p[0], `b` projects onto `lc or `rc`. */
        ensures match r
            case Node(_, lc, rc) =>
                forall k :: 0 <= k < |b| - 1 ==>
                     b[1..][k] == siblingAt(p[1..][..k + 1], if p[0] == 0 then lc else rc).v
    {
        match r 
            case Node(_, lc, rc) => 
                forall (k : nat | 0 <= k < |b| - 1) 
                    ensures 
                        0 <= k < |b| - 1 ==> 
                             b[1..][k] == siblingAt(p[1..][..k + 1], if p[0] == 0 then lc else rc).v 
                {
                    if ( k == 0 ) {
                        //  for k == 0, we cannot use the simplification on first bit of path
                        //  for siblings, so we do it case by case.
                        if |p| == 1 {
                            //  Thanks Dafny.
                        } else {
                            //  We need to prove b[1..][0] == siblingAt(p[1..][..0 + 1], if p[0] == 0 then lc else rc).v

                            var child := if p[0] == 0 then lc else rc;

                            calc == {
                                siblingAt(p[1..][..1], child).v;
                                siblingAt([p[1]], child).v;
                                nodeAt([] + [1 - p[1]], child).v;
                                calc == {
                                    [] + [1];
                                    [1];
                                }
                                nodeAt([1 - p[1]], child).v;
                                calc == {
                                    [] + [1];
                                    [1];
                                }
                                nodeAt([p[0], 1 - p[1]], r).v;
                                siblingAt([p[0] , p[1]], r).v;
                                b[1];
                            }
                        }
                    } else {
                        assert( k >= 1 );
                        var child := if p[0] == 0 then lc else rc ;
                        calc == {   //  These terms are equal
                            b[1..][k] ;
                            b[k + 1];
                            siblingAt(p[..k + 1 + 1], r).v;
                            { simplifySiblingAtFirstBit(p[..k + 1 + 1], r) ; }
                            siblingAt(p[..k + 1 + 1][1..], child).v;
                            //  Next step holds because of this equality:
                            calc == {
                                p[..k + 1 + 1][1..];
                                p[1..][..k + 1];
                            }
                            siblingAt(p[1..][..k + 1], child).v;
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
    lemma {:induction p, r, b} computeOnPathYieldsRootValue<T>(p : seq<bit>, r : Tree<T>, b : seq<T>, f : (T,T) -> T, seed: T) 
        requires 1 <= |p| == height(r) - 1
        requires isCompleteTree(r)
        /** `r` is decorated with attribute `f`. */
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
            
            
            match r
                case Node(_, lc, rc) =>

                // cby definition r.v == f(lc.v, rc.v)
                //  We show that whatever child is on path `p`  we have 
                //  the value of the sibling.

                var child := if p[0] == 0 then lc else rc ;
                var a := if p[0] == 0 then 1 else 0;

                //  this ensures we can use computeOnPathYieldsRootValue inductively
                //  it proves that b[1..][i] == siblingAt(p[1..][.. i + 1], r).v
                projectValuesOnChild(p, r, b);
                
                //  Induction on lc or rc depending on p[0]
                computeOnPathYieldsRootValue(p[1..], child, b[1..], f, seed);
                // this implies that if p[0] == 0 then lc.v else rc.v == 
                //                           computeRootPath(p[1..], b[1..], f, seed))

                calc == {
                    b[0] ;
                    nodeAt([] + [a], r).v;
                    calc == {  //  simplify
                        [] + [a];
                        [a];
                    }
                    nodeAt([a], r).v;
                    (if p[0] == 0 then rc.v else lc.v);
                }
        }
    }

 }