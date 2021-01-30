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
    function {:opaque} power2(n : nat): nat 
        ensures power2(n) >= 1
        ensures n >= 1 ==> power2(n) >= 2 

        decreases n
    {
        if n == 0 then 1 else 2 * power2(n - 1)
    }

    /** 
     *  Useful lemmas: 
     *      (2^n) * (2^n) == 2 ^(n + 1)
     *      2 * 2^n == 2^n * 2 == 2^(n + 1)
     */
    lemma {:induction n} {:opaque} power2Lemmas(n : nat) 
        ensures power2(n) + power2(n) == power2(n + 1)
        ensures 2 * power2(n) == power2(n) * 2 == power2(n + 1)
    {   //  Thanks Dafny
        reveal_power2();
    }

    /**
     *  2^(n + 1) / 2 == 2^n
     */
    lemma {:induction n} power2Div2(n : nat)
        requires n >= 1
        ensures power2(n) / 2 == power2(n - 1)
    {
        reveal_power2();
    }

    /**
     *  if k < 2^(n + 1) then k / 2 < 2^n
     */
    lemma {:induction n} power2Div2LessThan(k : nat, n : nat)
        requires n >= 1
        requires k < power2(n)
        ensures k / 2 < power2(n - 1)
    {
        reveal_power2();
    }

    /**
     *  If k < 2^{n} - 1 and the last bit of binary of k is 1, then
     *  k / 2 < 2^{n - 1} - 1
     */
    lemma {:induction n} power2LessThanDiv2(k : nat, n : nat) 
        requires n >= 1
        requires k < power2(n) - 1
        requires k % 2 == 1
        ensures k / 2 < power2(n - 1) - 1
    {
        reveal_power2();   
    }
}
