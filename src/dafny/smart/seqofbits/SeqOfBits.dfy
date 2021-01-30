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

include "../helpers/Helpers.dfy"
include "../helpers/SeqHelpers.dfy"

/** 
 *  Provide seq<bit>.
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
        reveal_power2();
        if |p| == 1 then 
            first(p) as nat
        else 
            if first(p) == 1 then 
                power2(|p| - 1) + bitListToNat(tail(p))
            else 
                 bitListToNat(tail(p))
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
        reveal_power2();
        if length == 1 then
            [n as bit] 
        else 
            natToBitList(n / 2, length - 1) +  [(n % 2) as bit]
    }

    function natToBitList2(n: nat, length: nat) : seq<bit> 
        // requires 0 <= length 
        /** Number of bits is sufficient to encode `n`. */
        requires n < power2(length)
        ensures |natToBitList2(n, length)| == length
        ensures length >= 1 ==> natToBitList2(n, length) == natToBitList(n, length)
        decreases length
    {
        reveal_power2();
        if length == 0 then
            [] 
        else 
            natToBitList2(n / 2, length - 1) +  [(n % 2) as bit]
    }

    /**
     *  Combine two sequences of equal length using a condition.
     *  
     *  @param  a   A sequence.
     *  @param  b   A sequence.
     *  @param  c   A sequence of truth values.
     *  @returns    The sequence d such that d[i] = if c[i] then a[i] else b[i].
     */
    function zipCond<T>(c : seq<bit>, a : seq<T>, b : seq<T>) : seq<T>
        requires |a| == |b| == |c|
        ensures |zipCond(c, a, b)| == |a|
        ensures forall i :: 0 <= i < |a| ==>
            zipCond(c, a, b)[i] == if c[i] == 0 then a[i] else b[i]
        decreases |a|
    {
        if |a| == 0 then    
            []
        else 
            [if c[0] == 0 then a[0] else b[0]] + zipCond(tail(c), tail(a), tail(b))
    }

    /** 
     *  Compute a path (to next leaf) recursively from end.
     *  Alternatively binary add one on seq<bit>.
     *
     *  @param  p   A sequence of bits.
     *  @returns    The sequence encoding p + 1 (in binary).
     *  
     *  @note       Lemma nextPathIsSucc proves that 
     *              bitListToNat(nextPath(p)) == bitListToNat(p) + 1.
     */
    function nextPath(p : seq<bit>) : seq<bit> 
        /** Path has at least on element. */
        requires |p| >= 1
        /** Not the path 1+ that has no successors. */
        requires exists i :: 0 <= i < |p| && p[i] == 0
        ensures |nextPath(p)| == |p|

        decreases p
    {
        if last(p) == 0 then 
            init(p) + [1]
        else 
            nextPath(init(p)) + [0]
    }

    /**
     *  Involution theorem.

     *  bitListToNat(natToBitList(x)) == x.
     */
    lemma {:induction n} bitToNatToBitsIsIdentity(n : nat, length: nat) 
        requires length >= 1
        requires n < power2(length)
        ensures bitListToNat(natToBitList(n, length)) == n 
        ensures bitListToNat(natToBitList2(n, length)) == n 
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
     *  The prefix of p encodes n / 2.
     */
    lemma {:induction n, p} div2IsInit(n : nat,  p : seq<bit>)
        requires |p| >= 1
        requires n < power2(|p|)
        requires p == natToBitList2(n, |p|)
        ensures init(p) == natToBitList2(n / 2, |p| - 1)
    {   //  Thanks Dafny        
    }

    /**
     *  If p is the path that represents n (over length bits), 
     *  then nextPath(p) is the path that represents n + 1.
     */
    lemma {:induction p, n, length} pathToSucc(p : seq<bit>, n : nat, length: nat)
        requires length >= 1
        requires n < power2(length) - 1
        requires p == natToBitList(n, length)
        ensures exists i :: 0 <= i < |p| && p[i] == 0  
        ensures nextPath(p) == natToBitList(n + 1, length)
    {
        bitToNatToBitsIsIdentity(n, length);
        assert(bitListToNat(p) == n < power2(length) - 1 == power2(|p|) - 1);
        pathToNoLasthasZero(p);
    }
        
    /**
     *  (In)equalities between  bitListToNat(tail(p)) and bitListToNat(p).
     */
    lemma {:induction p} bitListOfTailForFirstZero(p : seq<bit>)
        requires |p| >= 2
        requires first(p) == 0
        ensures  first(p) == 0 ==> bitListToNat(tail(p)) == bitListToNat(p)
        ensures  first(p) == 1 ==> bitListToNat(tail(p)) <= bitListToNat(p) / 2
    {   //  Thanks Dafny
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
            var p' := p + [a];
            var f := if first(p') == 1 then power2(|p'| - 1) else 0;
            //  note that power2(|p'| - 1) == power2(|p|)
            calc == {
                tail(p');
                tail(p) + [a];
            }
            calc == {
                bitListToNat(p');
                { seqLemmas(p') ;}
                bitListToNat([first(p')]+ tail(p'));
                f + bitListToNat(tail(p'));
                f + bitListToNat(tail(p'));
                f + bitListToNat(tail(p) + [a]);
                //  Induction on tail(p)
                { simplifyPrefixBitListToNat(tail(p), a) ; }
            }
        }
    }

    //  Some properties of seq<bit> that encode paths in a binary tree.

    /**
     *  The number represented by nextPath(p) is the successor of the
     *  number represented by `p`.
     *
     *  @param  p   A path.
     */
    lemma {:induction p} nextPathIsSucc(p : seq<bit>)
        /** Path has at least one element. */
        requires |p| >= 1
        /** It is not the path 1+ that has no successors. */
        requires exists i :: 0 <= i < |p| && p[i] == 0
        ensures bitListToNat(nextPath(p)) == bitListToNat(p) + 1
        decreases p
    {
        if |p| == 1 {
            //  Thanks Dafny
        } else {
            //  we want to prove bitListToNat(nextPath(p)) ==  bitListToNat(p) + 1
            if last(p) == 0 {
                calc == {
                    bitListToNat(p);
                    { seqLemmas(p) ; }
                    bitListToNat(init(p) + [0]);
                    { simplifyPrefixBitListToNat(init(p), 0) ;}
                    2 * bitListToNat(init(p));
                }
                //  Simplify bitListToNat according to last(p)
                calc == {
                    bitListToNat(nextPath(p));
                    { seqLemmas(p) ; }
                    bitListToNat(init(p) + [1]);
                    { simplifyPrefixBitListToNat(init(p), 1); }
                    2 * bitListToNat(init(p)) + 1;
                    // which is bitListToNat(p) + 1;
                } 
            } else {
                //  last of p is 1
                assert(last(p) == 1);
                //  p == init(p) + [1]
                calc == {
                    p ;
                    { seqLemmas(p) ; }
                    init(p) + [last(p)];
                    init(p) + [1];
                }
                //  Simplify bitListToNat(p) according to last(p)
                calc == {
                    bitListToNat(p);
                    bitListToNat(init(p) + [1]);
                    { simplifyPrefixBitListToNat(init(p), 1); }
                    2 * bitListToNat(init(p)) + 1 ;
                }
                calc == {
                    bitListToNat(nextPath(p));
                    bitListToNat(nextPath(init(p) + [1]));
                    == { simplifyPrefixBitListToNat(nextPath(init(p)), 0);}
                    2 * bitListToNat(nextPath(init(p)));
                    == { nextPathIsSucc(init(p)) ; } 
                    2 * (bitListToNat(init(p)) + 1) ;
                    // which is bitListToNat(p) + 1;
                }
            }
        }
    } 

    /**
     *  If two paths denote the same the number, they are identical.
     *  
     *  @param  p    A path.
     *  @param  p'   A path.
     */
    lemma {:induction p, p'} sameNatSameBitList(p : seq<bit>, p' : seq<bit>)
        requires 1 <= |p| == |p'| 
        requires bitListToNat(p') == bitListToNat(p)
        ensures p' == p
        decreases p 
    {
        if |p| == 1 {
            //  Thanks Dafny
        } else {
            //  Show that last(p) == last(p') 
            calc == {
                    bitListToNat(p); 
                    { seqLemmas(p); }
                    bitListToNat(init(p) + [last(p)]);
                    { simplifyPrefixBitListToNat(init(p), last(p)); }
                    2 *  bitListToNat(init(p)) + last(p) as nat;
                }
            assert(bitListToNat(p) % 2 == last(p) as nat % 2  );
            calc == {
                bitListToNat(p'); 
                { seqLemmas(p'); }
                bitListToNat(init(p') + [last(p')]);
                { simplifyPrefixBitListToNat(init(p'), last(p')); }
                2 *  bitListToNat(init(p')) + last(p') as nat;
                }
            assert(bitListToNat(p) % 2 == last(p') as nat % 2  );
            assert(last(p') as nat % 2 == last(p) as nat % 2);
            assert(last(p) == last(p'));

            //  Now we can also prove that bitListToNat(init(p')) == bitListToNat(init(p))
            assert(bitListToNat(init(p')) == bitListToNat(init(p)));

            //  And apply sameNatSameBitList
            calc == {
                p;
                { seqLemmas(p); }
                init(p) + [last(p)];
                { sameNatSameBitList(init(p), init(p')); }
                init(p') + [last(p')];
                { seqLemmas(p'); }
                p';
            }
        }
    }

    /**
     *  If two paths denote successive numbers, one is the succ of the other.
     *  
     *  @param  p    A path.
     *  @param  p'   A path.
     */
    lemma {:induction p, p'} succIsNextPath(p : seq<bit>, p' : seq<bit>)
        /** Path has at least one element. */
        requires 1 <= |p| == |p'| 
        /** It is not a path that has no successors and must have a zero. */
        requires exists i :: 0 <= i < |p| && p[i] == 0
        requires bitListToNat(p') == bitListToNat(p) + 1
        ensures p' == nextPath(p)
        decreases p
    {
        if |p| == 1 {
            //  Thanks Dafny
        } else {
            if last(p) == 0 {
                // init(p) + [1]
                // bitListToNat(p + [a]) == 2 * bitListToNat(p) + a as nat
                calc == {
                    nextPath(p);
                    init(p) + [1];
                }
                //  Show that last(p) == 1
                //  First bitListToNat(p) + 1 is odd.
                calc == {
                    bitListToNat(p) + 1; 
                    { seqLemmas(p); }
                    bitListToNat(init(p) + [last(p)]) + 1;
                    // {} 
                    bitListToNat(init(p) + [0]) + 1;
                    { simplifyPrefixBitListToNat(init(p), 0); }
                    2 *  bitListToNat(init(p)) + 0 as nat + 1;
                    2 *  bitListToNat(init(p)) + 1;
                }
                assert( (bitListToNat(p) + 1) % 2 == 1);
                //  Assume 
                if last(p') == 0 {
                    //  In this case we show that bitListToNat(p') is even
                    calc == {
                        bitListToNat(p') ;
                        { seqLemmas(p'); }
                        bitListToNat(init(p') + [last(p')]);
                        { simplifyPrefixBitListToNat(init(p'), 0); }
                        2 * bitListToNat(init(p')) + 0;
                    }
                    assert(bitListToNat(p') % 2 == 0);
                    //  because bitListToNat(p') == bitListToNat(p) + 1
                    //  it cannot be odd and even
                    assert(false);
                }
                assert(last(p') == 1);
                //  Now we need to show that init(p) == init(p')
                //  First show that bitListToNat(init(p')) == bitListToNat(init(p))
                calc == {
                    bitListToNat(p) + 1;
                    2 *  bitListToNat(init(p)) + 1;
                }
                calc == {
                    2 *  bitListToNat(init(p)) + 1;
                    bitListToNat(p) + 1;
                    bitListToNat(p') ;
                    { seqLemmas(p'); }
                    bitListToNat(init(p') + [last(p')]);
                    { simplifyPrefixBitListToNat(init(p'), 1); }
                    2 * bitListToNat(init(p')) + 1;
                }
                assert(bitListToNat(init(p')) == bitListToNat(init(p)));
                //  Then use sameNatSameBitList to conclude that init(p) == init(p')
                calc == {
                    nextPath(p);
                    init(p) + [1];
                    { sameNatSameBitList(init(p), init(p')) ; }
                    init(p') + [1] ;
                    init(p') + [last(p')];
                    { seqLemmas(p'); }
                    p';
                }
            } else {
                assert(last(p) == 1);
                //  last(p) is not zero, so there is a zero in prefix
                pushExistsToInitPrefixIfNotLast(p);
                assert(exists i :: 0 <= i < |init(p)|  && init(p)[i] == 0);

                //  Show that last(p') == 0
                //  First bitListToNat(p) + 1 is even.
                calc == {
                    bitListToNat(p) + 1; 
                    { seqLemmas(p); }
                    bitListToNat(init(p) + [last(p)]) + 1;
                    // {} 
                    bitListToNat(init(p) + [1]) + 1;
                    { simplifyPrefixBitListToNat(init(p), 1); }
                    2 *  bitListToNat(init(p)) + 1 as nat + 1;
                    2* (bitListToNat(init(p)) + 1);
                }
                assert( (bitListToNat(p) + 1) % 2 == 0 );
                //  Assume 
                if last(p') == 1 {
                    //  In this case we show that bitListToNat(p') is odd
                    calc == {
                        bitListToNat(p') ;
                        { seqLemmas(p'); }
                        bitListToNat(init(p') + [last(p')]);
                        { simplifyPrefixBitListToNat(init(p'), 1); }
                        2 * bitListToNat(init(p')) + 1;
                    }
                    assert(bitListToNat(p') % 2 == 1);
                    //  because bitListToNat(p') == bitListToNat(p) + 1
                    //  it cannot be odd and even
                    assert(false);
                }
                assert(last(p') == 0);
                //  Show that bitListToNat(init(p')) == bitListToNat(init(p)) + 1
                calc == {
                    2* (bitListToNat(init(p)) + 1);
                    2 *  bitListToNat(init(p)) + 1 as nat + 1;
                    bitListToNat(p) + 1;
                    bitListToNat(p');
                    { seqLemmas(p'); }
                    bitListToNat(init(p') + [last(p')]);
                    { simplifyPrefixBitListToNat(init(p'), 0); }
                    2 * bitListToNat(init(p'));
                }
                //  Dividing by two implies: 
                assert(bitListToNat(init(p')) == bitListToNat(init(p)) + 1);
                calc == {
                    nextPath(p);
                    nextPath(init(p)) + [0];
                    //  Induction on init(p), init(p') : init(p') == nextPath(init(p))
                    { succIsNextPath(init(p), init(p')); }
                    init(p') + [0];
                    init(p') + [last(p')];
                    p';
                }
            }
        }
    }

     /**
     *  A path is the next path of another iff they denote successive numbers.
     *  
     *  @param  p    A path.
     *  @param  p'   A path.
     */
    lemma {:induction p, p'} nextPathIffSucc(p : seq<bit>, p' : seq<bit>) 
        requires 1 <= |p| == |p'|
        requires exists i :: 0 <= i < |p| && p[i] == 0
        ensures p' == nextPath(p) <==> bitListToNat(p') == bitListToNat(p) + 1
    {
        if p' == nextPath(p) {
            nextPathIsSucc(p);
        } else if bitListToNat(p') == bitListToNat(p) + 1 {
            succIsNextPath(p, p');
        }
    } 


    /**
     *  If all bits are set,  bitListToNat(p) = 2^p - 1.
     */
    lemma {:induction p} valueOfSeqOfOnes(p : seq<bit>)
        requires |p| >= 1
        requires forall i :: 0 <= i < |p| ==> p[i] == 1
        ensures bitListToNat(p) == power2(|p|) - 1
    {   //  Thanks Dafny
    }

    /**
     *  If bitListToNat(p) == 0 then p has only zeroes.
     */
    lemma {:induction p} valueIsZeroImpliesAllZeroes(p : seq<bit>)
        requires |p| >= 1
        requires bitListToNat(p) == 0
        ensures forall i :: 0 <= i < |p| ==> p[i] == 0
    {   //  Thanks Dafny
    }

    /**
     *  If bitListToNat(p) < power2(|p|) - 1 then p has a zero.
     */
    lemma {:induction p} pathToNoLasthasZero(p : seq<bit>) 
        requires |p| >= 1
        requires bitListToNat(p) < power2(|p|) - 1
        ensures  exists i :: 0 <= i < |p| && p[i] == 0
    {
        calc ==> 
        {
            !(exists i :: 0 <= i < |p| && p[i] == 0);
            forall i :: 0 <= i < |p| ==> p[i] == 1;
            { valueOfSeqOfOnes(p); }
            bitListToNat(p) == power2(|p|) - 1;
            false;
        }
    }

    /**
     *  If a sequence contains a value and it is not the last, then it
     *  is in the prefix.
     */
    lemma {:induction p} pushExistsToInitPrefixIfNotLast(p : seq<bit>)
        requires |p| >= 2
        requires last(p) != 0
        requires exists i :: 0 <= i < |p| && p[i] == 0
        ensures  exists i :: 0 <= i < |p| - 1 && p[i] == 0
        ensures exists i :: 0 <= i < |init(p)|  && init(p)[i] == 0
    {
        //  Get a witness value for i
        var i :| 0 <= i < |p| && p[i] == 0;
        //  show that i < |p| - 1
        if ( i == |p| - 1) {
            //  impossible as last(p) != 0, assert false
            assert(false);
        } else {
            //  because i < |p|, and i != |p| - 1
            assert( i < |p| - 1);
            seqIndexLemmas(p, i);
        }
    }

    /**
     *  If last bit is 1, the prefixes of nextPath of init
     *  are the same as nextPath of p.
     */
    lemma {:induction p} prefixOfNextPathOfInitIsSameIfLastisOne(p : seq<bit>, k : nat)
        requires |p| >= 2
        requires last(p) == 1
        requires exists i :: 0 <= i < |p| && p[i] == 0
        requires 0 <= k < |p|
        ensures nextPath(init(p))[..k] == nextPath(p)[..k]
    {   //  Thanks Dafny
    }
    
}
