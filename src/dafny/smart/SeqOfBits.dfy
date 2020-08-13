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
     *  Encode a natural on length bits.
     *  
     *  @param  n       A non-negative integer.
     *  @param  length  A number of bits.
     */
    function natToBitList(n: nat, length: nat) : seq<bit> 
        requires 1 <= length 
        /** Number of bits is sufficient to encode `n`. */
        requires n < power2(length)
        ensures |natToBitList(n, length)| == length
        decreases length
    {
        if length == 1 then
            [n as bit] 
        else 
            natToBitList(n / 2, length - 1) +  [(n % 2) as bit]
    }

    /** 
     *  Compute a path (to next leaf) recursively from end.
     *  Alternatively binary add one on seq<bit>.
     *
     *  @param  p   A sequence of bits.
     *  @returns    The sequence encoding p + 1 (in binary).
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
     *  Involution theorem.

     *  bitListToNat(natToBitList(x)) == x.
     */
    lemma {:induction n} bitToNatToBitsIsIdentity(n : nat, length: nat) 
        requires length >= 1
        requires n < power2(length)
        ensures bitListToNat(natToBitList(n, length)) == n 
        decreases length
    {
        if length <= 1 {
            //  Thanks Dafny
        } else {
            calc == {
                bitListToNat(natToBitList(n, length));
                bitListToNat(natToBitList ( n / 2 , length - 1) + [(n % 2) as bit]);
                { simplifyPrefixBitListToNat(natToBitList( n / 2 , length - 1), (n % 2) as bit); }
                2 * bitListToNat(natToBitList ( n / 2, length - 1 )) + ((n % 2) as bit) as nat;
                { bitToNatToBitsIsIdentity( n / 2, length - 1 ); }
                2 * ( n / 2) + ((n % 2) as bit) as nat;
            }
        }
    }

    /**
     *  Relation between bitListToNat(p + x) and bitListToNat(x).
     *  
     *  @todo   A not-that-hard but very tedious proof.
     */
    lemma {:induction p} simplifyPrefixBitListToNat(p: seq<bit>, a : bit) 
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
                    //  induction on p[1..] available as simplifyPrefixBitListToNat(p[1..], a);
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
                    //  Induction on p[1..] available as simplifyPrefixBitListToNat(p[1..], a);
                }
            }
        }
    }

    //  Some properties of seq<bit> that encode paths in a binary tree.

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
                //  we want bitListToNat(nextPath(p)) ==  bitListToNat(p) + 1
                calc == {
                    bitListToNat(p);
                    calc == {
                        p;
                        p[..|p| - 1] + [0];
                    }
                    bitListToNat(p[..|p| - 1] + [0]);
                    { simplifyPrefixBitListToNat(p[..|p| - 1], 0) ;}
                    2 * bitListToNat(p[..|p| - 1]);
                }
                calc == {
                    bitListToNat(nextPath(p));
                    calc == {
                        nextPath(p);
                        p[..|p| - 1] + [1];
                    }
                    bitListToNat(p[..|p| - 1] + [1]);
                    { simplifyPrefixBitListToNat(p[..|p| - 1], 1); }
                    2 * bitListToNat(p[..|p| - 1]) + 1;
                    bitListToNat(p) + 1;
                } 
            } else {
                //  we want bitListToNat(nextPath(p)) ==  bitListToNat(p) + 1
                //  last of p is 1
                calc == {
                    bitListToNat(p);
                    calc == {
                        p;
                        p[..|p| - 1] + [p[|p| - 1]];
                        { assert(p[|p| - 1] == 1); }
                        p[..|p| - 1] + [1];
                    }
                    bitListToNat(p[..|p| - 1] + [1]);
                    { simplifyPrefixBitListToNat(p[..|p| - 1], 1); }
                    2 * bitListToNat(p[..|p| - 1]) + 1 ;
                }
                calc == {
                    bitListToNat(nextPath(p));
                    calc == {
                        nextPath(p);
                        nextPath(p[..|p| - 1] + [1]);
                        nextPath(p[..|p| - 1]) + [0];
                    }
                    bitListToNat(nextPath(p[..|p| - 1]) + [0]);
                    == { simplifyPrefixBitListToNat(nextPath(p[..|p| - 1]), 0);}
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