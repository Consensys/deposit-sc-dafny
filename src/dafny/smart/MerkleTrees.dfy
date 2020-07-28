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
include "Trees.dfy"

module MerkleTrees {

    import opened Helpers
    import opened Trees
 
    /**
     *  
     *  @param  l       A list of elements.
     *  @param  root    A tree.
     *  @param  default The default vakue for right-padding the tree leaves.
     *
     *  We assume collectLeaves return an indexed from left to right list of leaves.
     *
     *  @todo           We can use another function that returns the values instead
     *                  of collectleaves (returns the seq of values directly) and then
     *                  no need for `x.v`.
     */
    predicate treeLeftmostLeavesMatchList<T>(l: seq<T>, root: Tree<T>, default: T)
        requires |l| <= |collectLeaves(root)|
    {
        forall i:: 
            (0 <= i < |l| ==> l[i] == collectLeaves(root)[i].v)
            && 
            (|l| <= i < |collectLeaves(root)|  ==> collectLeaves(root)[i].v == default)
    }
}
