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
 
include "../trees/CompleteTrees.dfy"
include "../helpers/Helpers.dfy"
include "../paths/PathInCompleteTrees.dfy"
include "../seqofbits/SeqOfBits.dfy"
include "../helpers/SeqHelpers.dfy"
include "../trees/Trees.dfy"

/**
 *  Provide proofs that right siblings are constant in Merkle like trees.
 */
module RSiblings {
   
    import opened CompleteTrees
    import opened Helpers
    import opened PathInCompleteTrees
    import opened SeqOfBits
    import opened SeqHelpers
    import opened Trees

    /**
     *  Default values on each evel of a tree.
     *
     *  Values are obtained by conbining the default values at level h - 1.
     *  @param  f   The synthesied attribute to compute.
     *  @param  d   The default value attached to the leaves.
     *  @param  h   The height of the tree.
     *
     */  
    function defaultValue<T>(f: (T, T) -> T, d: T, h : nat) : T
        decreases h
    {
        if h == 0 then 
            d
        else 
            var x := defaultValue(f, d, h - 1);
            f(x, x)
    }

    function method zeroes<T>(f: (T, T) -> T, d: T, h : nat) : seq<T>
        decreases h 
        ensures |zeroes(f, d, h)| == h + 1
        ensures forall i {:induction i}:: 0 <= i < |zeroes(f, d, h)| ==> zeroes(f, d, h)[i] == defaultValue(f, d, h - i) 
    {
        if h == 0 then 
            [d]
        else 
            var xs := zeroes(f, d, h - 1);
            [f(xs[0], xs[0])] + xs
    }

    /**
     *  Prefix of zeroes if zeroes of f(d,d).
     */
    lemma {:induction h} shiftZeroesPrefix<T>(h : nat, f  : (T, T) -> T, d: T)
        requires 1 <= h 
        ensures init(zeroes(f, d, h)) == zeroes(f, f(d, d), h - 1)
    {   //  Thanks Dafny
    }

    /**
     *  In a complete tree, decorated with a synthesised attribute f,
     *  and all leaves have a default value,  
     *  the root is decorated with default applied height(r) times.
     *  
     *  @param  r   A complete tree.
     *  @param  f   A binary function.
     *  @param  d   A default value.
     */
    lemma {:induction r} allLeavesDefaultImplyRootNodeDefault<T>(r: Tree<T>, f: (T, T) -> T, d: T)
        requires isCompleteTree(r)
        requires isDecoratedWith(f, r)
        requires forall l :: l in leavesIn(r) ==> l.v == d
        ensures r.v == defaultValue(f, d, height(r))
        decreases r 
    {   
        if height(r) == 0 {
            // Thanks Dafny
        } else {
            match r
                case Node(_, lc, rc) => 
                //  Induction on left and richj children
                //  Leaves of left and right children are equal to d.
                childrenInCompTreesHaveHalfNumberOfLeaves(r, height(r));
                assert(leavesIn(lc) == leavesIn(r)[.. power2(height(r)) / 2]);
                assert(leavesIn(rc) == leavesIn(r)[power2(height(r)) / 2 ..]);
               
                calc == {
                    r.v;
                    f(lc.v, rc.v);
                    {
                        //  Induction on lc and rc
                        allLeavesDefaultImplyRootNodeDefault(lc, f, d);
                        allLeavesDefaultImplyRootNodeDefault(rc, f, d);
                    }
                    f(defaultValue(f, d, height(r) - 1), defaultValue(f, d, height(r) - 1));
                    defaultValue(f, d, height(r));
                }
        }
    }

    /**
     *  Given a tree decorated with synthesised attribute f, an index k to a leaf
     *  and the path p leading to this leaf, if all leaves at indices > k are default,
     *  then any right sibling at index i on p has default value for height(r) - (i + 1)
     *
     *  @param  p       A path to a leaf.
     *  @param  r       A complete tree.
     *  @param  k       The index of a leaf in r.
     *  @param  f       The synthesied attribute to compute.
     *  @param  index   The offset of the indexing of r.
     *  @param  d       The default value attached to the leaves.
     *  @param  i       An index on path p.
     *    
     */
    lemma {:induction p, r} siblingsRightOfPathAreConstant<T>(p : seq<bit>, r : Tree<T>, k : nat, f: (T, T) -> T, index : nat, d : T, i : nat) 

        requires isCompleteTree(r)
        requires isDecoratedWith(f, r)
        requires hasLeavesIndexedFrom(r, index)

        /**  all leaves after index k leaf have default value. */
        requires k < |leavesIn(r)|
        requires forall i :: k < i < |leavesIn(r)| ==> leavesIn(r)[i].v == d

        /** p is the path to k leaf in r. */
        requires 1 <= |p| == height(r)
        requires bitListToNat(p) == k 

        requires 0 <= i < |p|
        ensures p[i] == 0 ==> siblingValueAt(p, r, i + 1) == defaultValue(f, d, height(r) - (i + 1))

        decreases r
    {
        if p[i] == 0 {
            //  if tree height 1 easy else split i == 0 and i >= 1 (induction)
            if height(r) == 1 {
                    calc == {
                        |p|;
                        height(r);
                        1;
                    }
                    calc == {
                        p;
                        [p[0]];
                        [0];
                    }
                    calc == {
                        siblingValueAt(p, r, i + 1);
                        { reveal_siblingValueAt(); }
                        siblingAt(take(p, i + 1), r).v;
                        { assert( i == 0); }
                        siblingAt(take(p, 1), r).v;
                        calc == {
                            take(p, 1);
                            [p[0]];
                            [0];
                        }
                        siblingAt([0], r).v;
                        calc == {
                            init([0]) + [1];
                            [1];
                        }
                        nodeAt([1], r).v;
                        //  same as leaf at index 1
                        leavesIn(r)[1].v;
                        d;
                        defaultValue(f, d, height(r) - (i + 1));
                    }
            } else {
                if (i == 0) {
                    match r 
                        case Node(_, lc, rc) => 
                            //  first index of path is 0. All leaves in rc have default value d.
                            //  Hence root of rc has default value 
                            
                            //  Leaves of left and right children are equal to d.
                            childrenInCompTreesHaveHalfNumberOfLeaves(r, height(r));
                            assert(leavesIn(lc) == leavesIn(r)[.. power2(height(r)) / 2]);
                            assert(leavesIn(rc) == leavesIn(r)[power2(height(r)) / 2 ..]);
                            assert(
                                forall l :: l in leavesIn(rc) ==> l.v == d
                            );
                            allLeavesDefaultImplyRootNodeDefault(rc, f, d);
                            assert(rc.v == defaultValue(f, d, height(rc)));
                            calc == {
                                siblingValueAt(p, r, i + 1);
                                siblingValueAt(p, r, 1);
                                { reveal_siblingValueAt(); }
                                siblingAt(take(p, 1), r).v;
                                calc == {
                                    take(p, 1);
                                    [p[0]];
                                    [0];
                                }
                                siblingAt([0], r).v;
                                calc == {
                                    init([0]) + [1];
                                    [1];
                                }
                                nodeAt([1], r).v;
                                rc.v; 
                                { allLeavesDefaultImplyRootNodeDefault(rc, f, d); }
                                defaultValue(f, d, height(rc));
                                defaultValue(f, d, height(r) - (i + 1));
                        
                            }
                } else {
                    assert(height(r) >= 2);
                    assert(i >= 1);
                    assert(|p| >= 2);
                    //  i is an index on p either in lc or rc. Apply induction on rc or lc
                    childrenInCompTreesHaveHeightMinusOne(r);
                    match r 
                        case Node(_, lc, rc) => 
                            //  Leaves of left and right children are equal to d.
                            childrenInCompTreesHaveHalfNumberOfLeaves(r, height(r));
                            assert(leavesIn(lc) == leavesIn(r)[.. power2(height(r)) / 2]);
                            assert(leavesIn(rc) == leavesIn(r)[power2(height(r)) / 2 ..]);
                            if (first(p) == 0) {
                                //  p[i] is in lc
                                initPathDeterminesIndex(r, p, k, index);
                                assert(k < power2(height(r)) / 2);
                                assert(k < |leavesIn(lc)|); 
                                
                                calc == {
                                    siblingValueAt(p, r, i + 1);
                                    { reveal_siblingValueAt(); }
                                    siblingAt(take(p, i + 1), r).v;
                                    { simplifySiblingAtIndexFirstBit(p, r, i + 1);}
                                    siblingAt(take(tail(p), i), lc).v;
                                    { reveal_siblingValueAt(); }
                                    siblingValueAt(tail(p), lc, i);
                                    { siblingsRightOfPathAreConstant(tail(p), lc, k, f, index, d, i - 1); }
                                    defaultValue(f, d, height(r) - (i + 1));
                                }
                            } else {
                                //  p[i] is in rc
                                initPathDeterminesIndex(r, p, k, index);
                                assert(k - power2(height(r)) / 2 < power2(height(r)) / 2);
                                assert(k - power2(height(r)) / 2 < |leavesIn(rc)|); 
                                
                                calc == {
                                    siblingValueAt(p, r, i + 1);
                                    { reveal_siblingValueAt(); }
                                    siblingAt(take(p, i + 1), r).v;
                                    { simplifySiblingAtIndexFirstBit(p, r, i + 1);}
                                    siblingAt(take(tail(p), i), rc).v;
                                    { reveal_siblingValueAt(); }
                                    siblingValueAt(tail(p), rc, i);
                                    { siblingsRightOfPathAreConstant(tail(p), rc, k - power2(height(r)) / 2, f, index + power2(height(r)) / 2, d, i - 1); }
                                    defaultValue(f, d, height(r) - (i + 1));
                                }
                            }
                }
            }
        }
    }

    /**
     *  Given a tree decorated with synthesised attribute f, an index k to a leaf
     *  and the path p leading to this leaf, if all leaves at indices > k are default,
     *  the values of the right siblings are the list of zeroes. 
     *
     *  @param  p       A path to a leaf.
     *  @param  r       A complete tree.
     *  @param  k       The index of a leaf in r.
     *  @param  f       The synthesised attribute to compute.
     *  @param  index   The offset of the indexing of r.
     *  @param  d       The default value attached to the leaves.
     *  @param  zeroes  The default f-value for each level.
     *    
     */
    lemma {:induction false} {:timeLimitMultiplier 2} rightSiblingsOfLastPathAreDefault<T>(p : seq<bit>, r : Tree<T>, k : nat, f: (T, T) -> T, index : nat, d : T) 
        requires isCompleteTree(r)
        requires isDecoratedWith(f, r)

        /**  all leaves after index k leaf are zero. */
        requires k < |leavesIn(r)|
        requires forall i :: k < i < |leavesIn(r)| ==> leavesIn(r)[i].v == d

        /** p is the path to k leaf in r. */
        requires hasLeavesIndexedFrom(r, index)
        requires 1 <= |p| == height(r)
        requires bitListToNat(p) == k 

        ensures forall i :: 0 <= i < |p| && p[i] == 0 ==> 
            siblingValueAt(p, r, i + 1) == zeroes(f, d, height(r) - 1)[i]
    {
        forall(i : nat | 0 <= i < |p|) 
            ensures p[i] == 0 ==> 
                siblingValueAt(p, r, i + 1) == zeroes(f, d, height(r) - 1)[i]
        {
            siblingsRightOfPathAreConstant(p, r, k, f, index, d, i);    
            if p[i] == 0 {
                 calc == {
                 siblingValueAt(p, r, i + 1);
                 { siblingsRightOfPathAreConstant(p, r, k, f, index, d, i);  }
                defaultValue(f, d, height(r) - (i + 1));
                calc == {
                    height(r) - 1 - i;
                    height(r) - (i + 1);
                }   
                defaultValue(f, d, (height(r) - 1) - i);
                zeroes(f, d, height(r) - 1)[i];
                }
            }  
        }
    }

 }