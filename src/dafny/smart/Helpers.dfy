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

module Helpers {

    /**
     *  Maximum of two non-negative integers.
     */
    function method max(x: nat, y : nat) : nat 
    {
        if x > y then 
            x
        else 
            y
    }

    //  Power of two stuff

    /** Define 2^n. */
    function power2(n : nat): nat 
        ensures power2(n) >= 1
        ensures n >= 1 ==> power2(n) >= 2 

        decreases n
    {
        if n == 0 then 1 else 2 * power2(n - 1)
    }

    /** 
     *  Usweful lemmas: 
     *      (2^n) * (2^n) == 2 ^(n + 1)
     *      2 * 2^n == 2^n * 2 == 2^(n + 1)
     */
    lemma {:induction n} power2Lemmas(n : nat) 
        ensures power2(n) + power2(n) == power2(n + 1)
        ensures 2 * power2(n) == power2(n) * 2 == power2(n + 1)
    {   //  Thanks Dafny
    }

    //  Bit vectors stuff.

    /**
     *  BitList to nat.
     *
     *  @param  p   A bitlist.
     *  @param  v   Initial value.
     *  @returns    The value v * power2(|p|) + the nat number that corresponds to
     *              bitVector `p` (little endian). 
     */
     function method bitListToNatAcc(p : seq<bool>, v: nat) : nat 
        ensures v * power2(|p|) <= bitListToNatAcc(p, v) < v * power2(|p|) + power2(|p|) 
        decreases p
    {
        if |p| == 0 then   
            v 
        else 
            bitListToNatAcc(p[1..], 2 * v + (if p[0] then 1 else 0))
    }

    /**
     *  The number represented by bitvector `p` little endian). 
     */
    function bitListToNat(p: seq<bool>) : nat 
        ensures 0 <= bitListToNat(p) < power2(|p|)
    {
        bitListToNatAcc(p, 0)
    } 

    /**
     *  Bounds for the unsigned nat represented by a bit vector.
     *
     */
    // lemma {:induction p} bitListToNatAccBound(p : seq<bool>, v: nat) 
    //     requires |p| >= 1
    //     ensures !p[0] ==> 0 <= bitListToNatAcc(p, v) < v * power2(|p|) + power2(|p| - 1) 
    //     ensures p[0] ==> v * power2(|p|) + power2(|p| - 1)  <= bitListToNatAcc(p, v) 
    // {
    //     if !p[0] {
    //         calc == {
    //             bitListToNatAcc(p, v) ;
    //             ==
    //             bitListToNatAcc(p[1..], 2 * v) ;
    //             <
    //             (2 * v) * power2(|p[1..]|) + power2(|p[1..]|);
    //             ==
    //             (2 * v) * power2(|p| - 1) + power2(|p| - 1);
    //             ==
    //             v * (2 * power2(|p| - 1)) + power2(|p| - 1);
    //             ==
    //             v * power2(|p|) + power2(|p| - 1);
    //         }
    //     }
    //     if p[0] {
    //         calc == {
    //             bitListToNatAcc(p, v) ;
    //             ==
    //             bitListToNatAcc(p[1..], 2 * v + 1) ;
    //             >=
    //             (2 * v + 1) * power2(|p[1..]|) ;
    //             ==
    //             (2 * v + 1) * power2(|p| - 1) ;
    //             ==
    //             2 * (v * power2(|p| - 1)) + power2(|p| - 1);
    //             ==
    //             v * power2(|p|) + power2(|p| - 1);
    //         }
    //     }
    // }

    /**
     *  The first digit of a bit vector splits possible values in two
     *  ranges.
     */
    // lemma {:induction p} firstDigitDeterminesRange(p : seq<bool>, v: nat)
    //     requires |p| >= 1
    //     ensures p[0] <==> v * power2(|p|) + power2(|p| - 1)  <= bitListToNatAcc(p, v) 
    // {
    //     bitListToNatAccBound(p, v);
    // }

    //  Seq helpers
    lemma prefixOfSuffixCommutes<T>(r: seq<T>, k : nat) 
        requires k < |r|
        requires |r| >= 1
        ensures r[..k + 1][1..] == r[1..][..k]    
    {}
}
