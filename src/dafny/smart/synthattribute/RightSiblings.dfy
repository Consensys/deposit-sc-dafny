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

    function zeroes<T>(f: (T, T) -> T, d: T, h : nat) : seq<T>
        decreases h 
        ensures |zeroes(f, d, h)| == h + 1
        ensures forall i :: 0 <= i < |zeroes(f, d, h)| ==> zeroes(f, d, h)[i] == defaultValue(f, d, h - i) 
    {
        if h == 0 then 
            [d]
        else 
            var xs := zeroes(f, d, h - 1);
            [f(xs[0], xs[0])] + xs
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

        /**  all leaves after index k leaf are zero. */
        requires k < |leavesIn(r)|
        requires forall i :: k < i < |leavesIn(r)| ==> leavesIn(r)[i].v == d

        /** p is the path to k leaf in r. */
        requires hasLeavesIndexedFrom(r, index)
        requires 1 <= |p| == height(r)
        requires bitListToNat(p) == k 

        requires 0 <= i < |p|
        ensures p[i] == 0 ==> siblingValueAt(p, r, i + 1) == defaultValue(f, d, height(r) - (i + 1))

        decreases r 
    {
        reveal_siblingValueAt();
        if height(r) == 0 {
            //  Although this case is not allowed by the pre conditions as height(r) >= 1,
            //  we can prove the property for it and the inductive case extends to 
            //  height(r) >= 1.
            //  Thanks Dafny
        } else if p[i] == 0 {
            //  |p| >= 1, induction on left and right child
            //  Prove pre-conditions hold for them
            match r 
                case Node(_, lc, rc) => 
                     //  Leaves of left and right children are equal to d.
                    childrenInCompTreesHaveHalfNumberOfLeaves(r, height(r));
                    assert(leavesIn(lc) == leavesIn(r)[.. power2(height(r)) / 2]);
                    assert(leavesIn(rc) == leavesIn(r)[power2(height(r)) / 2 ..]);
                    if first(p) == 0 {
                        initPathDeterminesIndex(r, p, k, index);
                        assert(k < power2(height(r)) / 2);
                        assert(k < |leavesIn(lc)|); 
                        //  Induction on lc
                        if i >= 1 {
                            //  sibling is in lc
                            calc == {
                                siblingAt(take(p, i + 1), r).v;
                                { simplifySiblingAtIndexFirstBit(p, r, i + 1);  }
                                siblingAt(take(tail(p), i), lc).v ;
                                //  induction
                                { siblingsRightOfPathAreConstant(tail(p), lc, k, f, index, d, i - 1);}
                                defaultValue(f, d, height(lc) - (i));
                            }
                        } else {
                            //  i == 0, first(p) == 0, the sibling is the rc.
                            calc == {
                                siblingAt(take(p, i + 1), r).v;
                                siblingAt(take(p, 0 + 1), r).v;
                                siblingAt([0], r).v;
                                calc == {
                                    [] + [1];
                                    [1];
                                }
                                nodeAt([1], r).v;
                                rc.v;
                                { allLeavesDefaultImplyRootNodeDefault(rc, f, d);}
                                defaultValue(f, d, height(rc));
                                defaultValue(f, d, height(r) - 1);
                            }
                        }
                    } else {
                        //  first(p) == 1, path in rc.
                        initPathDeterminesIndex(r, p, k, index);
                        assert(k >= power2(height(r)) / 2);
                        assert(k -  power2(height(r)) / 2 < |leavesIn(rc)|); 

                       //  Induction on rc
                        if i >= 1 {
                            //  sibling is in rc
                            calc == {
                                siblingAt(take(p, i + 1), r).v;
                                { simplifySiblingAtIndexFirstBit(p, r, i + 1);  }
                                siblingAt(take(tail(p), i), rc).v ;
                                //  induction
                                { siblingsRightOfPathAreConstant(tail(p), rc, k - power2(height(r)) / 2, f, index + power2(height(r)) / 2, d, i - 1);}
                                defaultValue(f, d, height(rc) - (i));
                            }
                        } else {
                            //  i == 0, as p[i] == p[0] == first(p), this case does not
                            //  occur as witnessed by asserting false here.
                            assert(false);
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
    lemma {:induction p, r} rightSiblingsOfLastPathAreDefault<T>(p : seq<bit>, r : Tree<T>, k : nat, f: (T, T) -> T, index : nat, d : T) 
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