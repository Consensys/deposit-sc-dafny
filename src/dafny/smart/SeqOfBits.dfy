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

}