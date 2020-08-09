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

include "Helpers.dfy"
include "SeqHelpers.dfy"

/** 
 *  Provide seq<bit>, functions and lemmas for it.
 */
module SeqOfBits {

    import opened Helpers
    import opened SeqHelpers

    /**
     *  A bit is an int that is 0 or 1.
     */
    newtype {:nativeType "int"} bit = i:int | 0 <= i < 2

    /**
     *  The number represented by bitvector `p` little endian). 
     *
     *  @param  p   A sequence of bits. 
     *  @returns    The unsigned int represented by `p`. 
     */
    function bitListToNat(p: seq<bit>) : nat 
        requires |p| >= 1
        decreases p
        ensures 0 <= bitListToNat(p) < power2(|p|)
    {
        if |p| == 1 then 
            p[0] as nat
        else 
            if p[0] == 1 then 
                power2(|p| - 1) + bitListToNat(p[1..])
            else 
                 bitListToNat(p[1..])
    } 

    
    /**
     *  Relation between bitListToNat( p + x) and bitListToNat(x).
     */
    lemma {:induction p} foo101(p: seq<bit>, a : bit) 
        requires |p| >= 1
        ensures bitListToNat(p + [a]) == 2 * bitListToNat(p) + a as nat
        decreases p
    {
        if |p| == 1 {
            //  Thanks Dafny
        } else {
            if p[0] == 1 {
                calc == {
                    bitListToNat(p + [a]) ;
                    == calc == {
                        p + [a];
                        ==
                        [p[0]] + p[1..] + [a];
                    }
                    bitListToNat([p[0]] + p[1..] + [a]);
                    == { seqAssoc([p[0]], p[1..], [a]) ; }
                    bitListToNat(([p[0]] + p[1..] + [a]));
                    == 
                    power2(|([p[0]] + p[1..] + [a])| - 1) + bitListToNat(([p[0]] + p[1..] + [a])[1..]);
                    == //  |([p[0]] + p[1..] + [a])| == |p| + 1
                    power2((|p| + 1) - 1) + bitListToNat(([p[0]] + p[1..] + [a])[1..]);
                    == calc == {
                        //  suffix of [p[0]] + p[1..] + [a])[1..] is p[1..] + [a]
                        ([p[0]] + p[1..] + [a])[1..] ;
                        == 
                        ([p[0]] + (p[1..] + [a]))[1..];
                        ==
                        p[1..] + [a];
                    }
                    power2((|p| + 1) - 1) + bitListToNat(p[1..] + [a]);
                    //  induction on p[1..] available as foo101(p[1..], a);
                }
            } else {
                //  p[0] == 0
                calc == {
                    bitListToNat(p + [a]) ;
                    == calc == {
                        p + [a];
                        ==
                        [p[0]] + p[1..] + [a];
                    }
                    bitListToNat([p[0]] + p[1..] + [a]);
                    ==
                    bitListToNat(([p[0]] + p[1..] + [a]));
                    == calc == {
                        ([p[0]] + p[1..] + [a])[0] ;
                        == 
                        p[0];
                    }
                    bitListToNat(([p[0]] + p[1..] + [a])[1..]);
                    == calc == {
                        ([p[0]] + p[1..] + [a])[1..] ;
                        == 
                        ([p[0]] + (p[1..] + [a]))[1..];
                        ==
                        p[1..] + [a];
                    }
                    bitListToNat(p[1..] + [a]);
                    //  Induction on p[1..] available as foo101(p[1..], a);
                }
            }
        }
    }

    //  Some properties of seq<bit> that encode paths in a binary tree.

    /** 
     *  Compute a path (to next leaf) recursively from end.
     *  
     *  @note   Lemma nextPathIsSucc provides a property of nextPath.
     */
    function nextPath(p : seq<bit>) : seq<bit> 
        /** Path has at least on element. */
        requires |p| >= 1
        /** Not the path 1+ that has no successors. */
        requires exists i :: 0 <= i < |p| && p[i] == 0
        ensures |nextPath(p)| == |p|

        decreases p
    {
        if p[|p| - 1] == 0 then 
            p[..|p| - 1] + [1]
        else 
           nextPath(p[.. |p| - 1]) + [0]
    }

    /**
     *  The number represented by nextPath(p) is the successor of the
     *  number represented by `p`.
     */
    lemma {:induction p} nextPathIsSucc(p : seq<bit>)
         /** Path has at least on element. */
        requires |p| >= 1
        /** It is not the path 1+ that has no successors. */
        requires exists i :: 0 <= i < |p| && p[i] == 0
        ensures bitListToNat(nextPath(p)) == bitListToNat(p) + 1
        decreases p
    {
        if |p| == 1 {
            //  Thanks Dafny
        } else {
            if p[|p| - 1] == 0 {
                assert(nextPath(p) == p[..|p| - 1] + [1]);
                assert( p == p[..|p| - 1] + [0]);
                foo101(p[..|p| - 1], 0);
                assert(bitListToNat(p) == 2 * bitListToNat(p[..|p| - 1]));
                foo101(p[..|p| - 1], 1);
                assert(bitListToNat(nextPath(p)) == 2 * bitListToNat(p[..|p| - 1]) + 1);
            } else {
                //  last of p is 1
                assert(p[|p| - 1] == 1);
                assert( p == p[..|p| - 1] + [1]);

                //  def of next path
                assert(nextPath(p) == nextPath(p[..|p| - 1]) + [0]);

                assert(exists i :: 0 <= i < |p| && i != |p| - 1 && p[i] == 0);
              
                assert(exists i :: 0 <= i < |p| - 1 && p[i] == 0);
                // This implies the pre-condition of this lemma on |p[..|p| - 1]|
                // Induction on p[..|p| - 1]
                assert(bitListToNat(nextPath(p[..|p| - 1])) == bitListToNat(p[..|p| - 1]) + 1);
                // //  binListToNat suffix
                foo101(p[..|p| - 1], 1);
                assert( bitListToNat(p) == 2 * bitListToNat(p[..|p| - 1]) + 1);

                calc {
                    bitListToNat(nextPath(p));
                    == 
                    bitListToNat(nextPath(p[..|p| - 1]) + [0]);
                    == { foo101(nextPath(p[..|p| - 1]), 0);}
                    2 * bitListToNat(nextPath(p[..|p| - 1]));
                    == { nextPathIsSucc(p[..|p| - 1]) ; } 
                    2 * (bitListToNat(p[..|p| - 1]) + 1) ;
                    ==
                    2 * bitListToNat(p[..|p| - 1]) + 2 ;
                    ==
                    (2 * bitListToNat(p[..|p| - 1]) + 1) + 1 ;
                    ==
                    bitListToNat(p) + 1;
                }
            }
        }
    } 

}