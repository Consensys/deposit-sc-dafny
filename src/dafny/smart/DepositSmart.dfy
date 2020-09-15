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

include "./trees/CompleteTrees.dfy"
include "./synthattribute/ComputeRootPath.dfy"
include "./synthattribute/RightSiblings.dfy"
include "./helpers/Helpers.dfy"
include "./paths/PathInCompleteTrees.dfy"
include "./paths/NextPathInCompleteTreesLemmas.dfy"
include "./seqofbits/SeqOfBits.dfy"
include "./helpers/SeqHelpers.dfy"
include "./trees/Trees.dfy"
include "./MerkleTrees.dfy"

module DepositSmart {

    import opened CompleteTrees
    import opened ComputeRootPath
    import opened RightSiblings
    import opened Helpers
    import opened NextPathInCompleteTreesLemmas
    import opened PathInCompleteTrees
    import opened SeqOfBits
    import opened SeqHelpers
    import opened Trees 
    import opened MerkleTrees

    /**
     *  
     *  @param  p       A path.
     *  @param  b       Values of nodes on left of p.
     *  @param  seed    The new value for the leaf at p.
     */
    // lemma {:induction p, b, seed} computeRootAndUpdateStateCommutes(p: seq<bit>, b : seq<int>, seed : int)
    //     requires 1 <= |p| == |b|
    //     ensures 
    //         var v1 := computeAllPathDiffUp(p, b, seed);
    //         var b' := computeLeftSiblingOnNextPathDep(p, b, seed);
    //             computeRootPathDiffUp(p, b', seed)
    //             == computeRootPathDiffUp(p, b, seed)
    // {   //  Thanks Dafny
    // }

    /**
     *  Compute the left siblings of nextPath from current values on left sibling.
     *
     *  @param  p       A path.
     *  @param  v2      The values of the nodes that are left siblings of nodes on the path.
     *  @param  seed    The value added to the leaf of the current path.
     *  @returns        The values of the nodes that are left siblings of nextPath(p).
     */
    // function method computeLeftSiblingOnNextPathDep(p: seq<bit>, v2 : seq<int>, seed: int) : seq<int>
    //     requires 1 <= |p| 
    //     requires |v2| == |p|
    //     ensures computeLeftSiblingOnNextPathDep(p, v2, seed) ==
    //         var v1 := computeAllPathDiffUp(p, v2, seed);
    //         computeLeftSiblingOnNextPath(p, v1, v2)

    //     decreases p
    // {
    //     if |p| == 1 then
    //         if first(p) == 0 then [seed] else v2 
    //     else 
    //         assert(|p| >= 2);
    //         if last(p) == 0 then 
    //             init(v2) + [diff(seed, 0)]
    //         else 
    //             assert(last(p) == 1);
    //             computeLeftSiblingOnNextPathDep(init(p), init(v2), diff(last(v2), seed)) + [last(v2)]
    // } 

    /**
     *  Compute the left siblings of nextPath from current values on left sibling.
     *  Same version as before but mixing in k anf h.
     *
     *  @param  p       A path.
     *  @param  v2      The values of the nodes that are left siblings of nodes on the path.
     *  @param  seed    The value added to the leaf of the current path.
     *  @param  h       Size of p.
     *  @param  k       The number represented by p on h bits.
     *  @returns        The values of the nodes that are left siblings of nextPath(p).
     */
    // function method computeLeftSiblingOnNextPathBridge(h : nat, k : nat, p: seq<bit>, v2 : seq<int>, seed: int) : seq<int>
    //     requires 1 <= |v2| == |p| == h

    //     requires k < power2(h)
    //     requires p == natToBitList2(k, h)

    //     ensures computeLeftSiblingOnNextPathBridge(h, k, p, v2, seed) ==
    //         var v1 := computeAllPathDiffUp(p, v2, seed);
    //         computeLeftSiblingOnNextPath(p, v1, v2)

    //     decreases p
    // {
    //     if |p| == 1 then
    //         if first(p) == 0 then [seed] else v2 
    //     else 
    //         assert(|p| >= 2);
    //         assert(|p| == h);
    //         if last(p) == 0 then 
    //             assert(k % 2 == 0);
    //             init(v2) + [diff(seed, 0)]
    //         else 
    //             assert(last(p) == 1);
    //             assert(k % 2 == 1);
    //             computeLeftSiblingOnNextPathBridge(h - 1, k / 2, init(p), init(v2), diff(last(v2), seed)) + [last(v2)]
    // } 

    //  Algorithms using k and h instead of the path p.

    /**
     *  Same version as before but without p.
     */
    // function method computeLeftSiblingOnNextPathFinal(h : nat, k : nat, v2 : seq<int>, seed: int) : seq<int>
    //     requires 1 <= |v2| == h

    //     requires k < power2(h)

    //     ensures 
    //         var p := natToBitList2(k, h );
    //         var v1 := computeAllPathDiffUp(p, v2, seed);
    //             computeLeftSiblingOnNextPathBridge(h, k, p, v2, seed) 
    //             ==
    //             computeLeftSiblingOnNextPathFinal(h, k, v2, seed)
    //             ==
    //             computeLeftSiblingOnNextPath(p, v1, v2)

    //     decreases h
    // {
    //     if h == 1 then
    //         if k % 2 == 0 then [seed] else v2 
    //     else 
    //         if k % 2 == 0 then 
    //             init(v2) + [diff(seed, 0)]
    //         else 
    //             computeLeftSiblingOnNextPathFinal(h - 1, k / 2, init(v2), diff(last(v2), seed)) + [last(v2)]
    // } 
    
    /**
     *  The functional version of the deposit smart contract.
     */
    class Deposit<T> {

        /** The default value for the leaves. */
        const d : T 

        /**
         *  The attribute function to synthesise.
         */
        const f : (T, T) -> T

        /** The height of the tree. */
        const TREE_HEIGHT : nat

        /** The values on the left siblings of the path to leaf of index k. */
        var branch : seq<T>

        /** The value sof the right siblings of path to leaf at index k. */
        const zeroes : seq<T>

        /** The number of values added to the list. Also the index of the next available leaf.
         */
        var count : nat 

        //  Ghost variables used for the correctness proof.

        /** The (Merkle) tree that corresponds to the list of values added so far. */
        ghost var t : Tree<T>

        /** The value of the root of the tree. */
        ghost var r : T

        /** The list of values added so far. */
        ghost var values : seq<T> 

        /** Path to current to the leaf of index count. */
        ghost var p : seq<bit>

        /** The array branch as a sequence. */
        // ghost var left : seq<int>

        //  Properties to maintain

        /** The list of values after count is default. */
        predicate listIsValid() 
            requires TREE_HEIGHT >= 1
            requires |values| == power2(TREE_HEIGHT)
            reads this
        {
            && forall k :: count <= k < |values| ==> values[k] == d
        }

        /** The tree t is the (Merkle) tree that corresponds to the list in values. */
        predicate treeIsMerkle()
            requires height(t) == TREE_HEIGHT
            requires |values| == |leavesIn(t)|
            reads this
        {
            isCompleteTree(t)
            && isDecoratedWith(f, t)
            && forall i :: 0 <= i < |values| ==> values[i] == leavesIn(t)[i].v    
            && hasLeavesIndexedFrom(t, 0)
        }

        /** Property to maintain. */
        predicate Valid()
            reads this
        {
            //  Height
            1 <= TREE_HEIGHT ==  height(t) == |branch| == |zeroes| == |p|
            //  tree is not full
            && count < power2(TREE_HEIGHT)

            && |values| == power2(TREE_HEIGHT) == |leavesIn(t)|

            //  zeroes is constant (@todo may remove this as declared const)
            && (forall i :: 0 <= i < |zeroes| ==> zeroes[i] ==  defaultValue(f, d, TREE_HEIGHT - (i + 1)))
            
            //  all leaves beyond count are default values
            && listIsValid()
            //  t is the Merkle tree that corresponds to values
            && treeIsMerkle()

            // && (r == t.v)
            && bitListToNat(p) == count
            && (forall i :: 0 <= i < |zeroes| && p[i] == 0 ==> 
                    siblingAt(take(p, i + 1), t).v == zeroes[i])
        }

        /**
         *  Initialise the system, tree of size >= 1.
         */
        constructor(h: nat, l : seq<T>, l' : seq<T>, tt: Tree<T>, default : T, fun : (T, T) -> T, z : seq<T>) 
            requires h >= 1
            requires |l| == power2(h) && forall i :: 0 <= i < |l| ==> l[i] == default
            requires |l'| == h && forall i :: 0 <= i < |l'| ==> l'[i] == default
            requires tt == buildMerkle(l, h, fun, default);
            requires |z| == h && forall i :: 0 <= i < |z| ==> z[i] == defaultValue(fun, default, h - (i + 1))
            ensures Valid()
        {
            TREE_HEIGHT := h;
            count := 0;
            d := default;
            f := fun;
            //  Initialise array with zeros
            // branch := new int[h](  (x: int) => 0 );
            //  
            branch := l';

            zeroes := z; 
            //  Initialise ghost variables
            values := l;

            //  possibly left could be left uninitialised
            // left := l';
            t := tt;
            p := natToBitList2(0, h);
            bitToNatToBitsIsIdentity(0, h);

            //  Initially r == default()
            r := defaultValue(fun, default, h);
            //  Use lemma to prove that r == t.v
            // allLeavesZeroImplyAllNodesZero(tt);
            allLeavesDefaultImplyRootNodeDefault(tt, fun, default);
            rightSiblingsOfLastPathAreDefault( natToBitList2(0, h), tt, 0, fun, 0, default, z);

        }

        /**
         *  Deposit a value i.e update the state.
         */
        method deposit(value : T) 
            requires Valid()
            requires count < power2(TREE_HEIGHT) - 1

            ensures Valid()
            
            modifies this

        {
            //   Update values
            values := values[count := value];
            //  Update tree
            t := buildMerkle(values, TREE_HEIGHT, f, d);

            //   update path 
            //   as p is to non last leaf it must have a zero and nextPath 
            //   can be computed
            bitToNatToBitsIsIdentity(count, TREE_HEIGHT);
            assert(bitListToNat(p) == count < power2(TREE_HEIGHT) - 1);
            pathToNoLasthasZero(p);
            nextPathIsSucc(p);
            assert(bitListToNat(nextPath(p)) == bitListToNat(p) + 1 == count + 1);
            p := nextPath(p);
            count := count + 1;

            //  p is still the path to leaf at index count
            bitToNatToBitsIsIdentity(count, TREE_HEIGHT);
            assert(bitListToNat(p) == count);

            //  Prove that right siblings of new path are still zeroes
            rightSiblingsOfLastPathAreDefault(p, t, count, f, 0, d, zeroes);
            
        }

    }

}