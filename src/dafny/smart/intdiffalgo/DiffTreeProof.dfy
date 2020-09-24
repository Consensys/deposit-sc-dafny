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

include "../intdiffalgo/DiffTree.dfy"

include "../helpers/Helpers.dfy"
include "../trees/Trees.dfy"
include "../MerkleTrees.dfy"
include "../seqofbits/SeqOfBits.dfy"
include "../trees/CompleteTrees.dfy"
include "../paths/PathInCompleteTrees.dfy"
include "../helpers/SeqHelpers.dfy"

module DiffTreeProof { 

    import opened Helpers
    import opened Trees
    import opened MerkleTrees
    import opened SeqOfBits
    import opened CompleteTrees
    import opened PathInCompleteTrees
    import opened SeqHelpers

    import opened DiffTree

    lemma leftSiblingsInMerkle(
            r: Tree<int>, 
            // l : seq<int>, 
            k: nat, 
            // b : seq<int>, 
            // f : (T, T) -> T,
            p :seq<bit>, 
            a : int,
            b : int,
            index: nat
            )
    
        //  Add this requirement first as otherwise the two requires
        //  isMerkle2 are very hard to prove and the solver may time out.
        requires 2 <= height(r)

        requires isCompleteTree(r)
        requires isDecoratedWith(diff, r)

        /** k is an index to a leaf of r. */
        requires k < power2(height(r) - 1)

        /** p is a path to k-th leave. */
        // requires nodeAt(p) == leavesIn(r)[k]

        // ensures       
    {

    }

}
