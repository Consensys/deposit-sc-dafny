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

include "Trees.dfy"
include "MerkleTrees.dfy"

module DepositTree {

    import opened Trees
    import opened MerkleTrees

    /** 
     *  Attribute hash.
     *
     */
    function hash<T>(a: T, b : T) : T 

    /**
     *  Check that a decorated tree correctly stores the diff attribute. 
     */
    predicate isDecoratedWithHash<T>(root: Tree<T>)
    {
        match root
            case Leaf(v, _, _) => true

            case Node(v, lc, rc, _, _) => v == hash(lc.v, rc.v)
    }

    /**
     *  Incremental algorithm.
     */
    class HashTree {

        /*
        * fun init() -> unit:
        *     i: int = 0
        *     while i < TREE_HEIGHT - 1:
        *         zerohashes[i+1] = hash(zerohashes[i], zerohashes[i])
        *         i += 1
        */

        /*
        * fun deposit(value: int) -> unit:
        *     assert deposit_count < 2^TREE_HEIGHT - 1
        *     deposit_count += 1
        *     size: int = deposit_count
        *     i: int = 0
        *     while i < TREE_HEIGHT - 1:
        *         if size % 2 == 1:
        *             break
        *         value = hash(branch[i], value)
        *         size /= 2
        *         i += 1
        *     branch[i] = value
        */

        /*
        * fun get_deposit_root() -> int:
        *     root: int = 0
        *     size: int = deposit_count
        *     h: int = 0
        *     while h < TREE_HEIGHT:
        *         if size % 2 == 1: # size is odd
        *             root = hash(branch[h], root)
        *         else:             # size is even
        *             root = hash(root, zerohashes[h])
        *         size /= 2
        *         h += 1
        *     return root
        */

} 
   


}
