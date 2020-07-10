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

    /** Define 2^n. */
    function power2(n : nat): nat 
        ensures power2(n) >= 1
        ensures n >= 1 ==> power2(n) >= 2 

        decreases n
    {
        if n == 0 then 1 else 2 * power2(n - 1)
    }

    /** 
     *  A simple lemma: (2^n) * (2^n) == 2 ^(n + 1)
     */
    lemma {:induction n} twoTimesPower2(n: nat) 
        ensures power2(n) + power2(n) <= power2(n + 1)
    {

    }
}
