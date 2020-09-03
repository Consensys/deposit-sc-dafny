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

include "../trees/CompleteTrees.dfy"
include "../synthattribute/ComputeRootPath.dfy"
include "../helpers/Helpers.dfy"
include "../paths/PathInCompleteTrees.dfy"
include "../paths/NextPathInCompleteTreesLemmas.dfy"
include "../seqofbits/SeqOfBits.dfy"
include "../helpers/SeqHelpers.dfy"
include "../trees/Trees.dfy"

module CommuteProofs {

    import opened DiffTree

    import opened CompleteTrees
    import opened ComputeRootPath
    import opened Helpers
    import opened NextPathInCompleteTreesLemmas
    import opened PathInCompleteTrees
    import opened SeqOfBits
    import opened SeqHelpers
    import opened Trees 

    /**
     *  
     *  @param  p       A path.
     *  @param  b       Values of nodes on left of p.
     *  @param  seed    The new value for the leaf at p.
     */
    lemma foo333(p: seq<bit>, b : seq<int>, seed : int)
        requires 1 <= |p| == |b|
        // requires v1 == computeAllPathDiffUp()
        ensures 
            var v1 := computeAllPathDiffUp(p, b, seed);
            var b' := computeLeftSiblingOnNextPath(p, v1, b);
                computeRootPathDiffUp(p, b', seed)
                == computeRootPathDiffUp(p, b, seed)
    {   //  Thanks Dafny
    }
    
}e 