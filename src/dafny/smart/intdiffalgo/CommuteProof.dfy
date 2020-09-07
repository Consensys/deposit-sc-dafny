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

include "../MerkleTrees.dfy"

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

    import opened MerkleTrees

    /**
     *  
     *  @param  p       A path.
     *  @param  b       Values of nodes on left of p.
     *  @param  seed    The new value for the leaf at p.
     */
    lemma {:induction p, b, seed} computeRootAndUpdateStateCommutes(p: seq<bit>, b : seq<int>, seed : int)
        requires 1 <= |p| == |b|
        ensures 
            var v1 := computeAllPathDiffUp(p, b, seed);
            var b' := computeLeftSiblingOnNextPathDep(p, b, seed);
                computeRootPathDiffUp(p, b', seed)
                == computeRootPathDiffUp(p, b, seed)
    {   //  Thanks Dafny
    }

    /**
     *  Compute the left siblings of nextPath from current values on left sibling.
     *
     *  @param  p       A path.
     *  @param  v2      The values of the nodes that are left siblings of nodes on the path.
     *  @param  seed    The value added to the leaf of the current path.
     *  @returns        The values of the nodes that are left siblings of nextPath(p).
     */
    function method computeLeftSiblingOnNextPathDep(p: seq<bit>, v2 : seq<int>, seed: int) : seq<int>
        requires 1 <= |p| 
        requires |v2| == |p|
        ensures computeLeftSiblingOnNextPathDep(p, v2, seed) ==
            var v1 := computeAllPathDiffUp(p, v2, seed);
            computeLeftSiblingOnNextPath(p, v1, v2)

        decreases p
    {
        if |p| == 1 then
            if first(p) == 0 then [seed] else v2 
        else 
            assert(|p| >= 2);
            if last(p) == 0 then 
                init(v2) + [diff(seed, 0)]
            else 
                assert(last(p) == 1);
                computeLeftSiblingOnNextPathDep(init(p), init(v2), diff(last(v2), seed)) + [last(v2)]
    } 

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
    function method computeLeftSiblingOnNextPathBridge(h : nat, k : nat, p: seq<bit>, v2 : seq<int>, seed: int) : seq<int>
        requires 1 <= |v2| == |p| == h

        requires k < power2(h)
        requires p == natToBitList2(k, h)

        ensures computeLeftSiblingOnNextPathBridge(h, k, p, v2, seed) ==
            var v1 := computeAllPathDiffUp(p, v2, seed);
            computeLeftSiblingOnNextPath(p, v1, v2)

        decreases p
    {
        if |p| == 1 then
            if first(p) == 0 then [seed] else v2 
        else 
            assert(|p| >= 2);
            assert(|p| == h);
            if last(p) == 0 then 
                assert(k % 2 == 0);
                init(v2) + [diff(seed, 0)]
            else 
                assert(last(p) == 1);
                assert(k % 2 == 1);
                computeLeftSiblingOnNextPathBridge(h - 1, k / 2, init(p), init(v2), diff(last(v2), seed)) + [last(v2)]
    } 

    //  Algorithms using k and h instead of the path p.

    /**
     *  Same version as before but without p.
     */
    function method computeLeftSiblingOnNextPathFinal(h : nat, k : nat, v2 : seq<int>, seed: int) : seq<int>
        requires 1 <= |v2| == h

        requires k < power2(h)

        ensures 
            var p := natToBitList2(k, h );
            var v1 := computeAllPathDiffUp(p, v2, seed);
                computeLeftSiblingOnNextPathBridge(h, k, p, v2, seed) 
                ==
                computeLeftSiblingOnNextPathFinal(h, k, v2, seed)
                ==
                computeLeftSiblingOnNextPath(p, v1, v2)

        decreases h
    {
        if h == 1 then
            if k % 2 == 0 then [seed] else v2 
        else 
            if k % 2 == 0 then 
                init(v2) + [diff(seed, 0)]
            else 
                computeLeftSiblingOnNextPathFinal(h - 1, k / 2, init(v2), diff(last(v2), seed)) + [last(v2)]
    } 
    
    /**
     *  The functional version of the deposit smart contract.
     */
    class Deposit {

        //  Versions of compute left siblings on compute root path using the
        //  height of the tree and the current leaf number

        /** The height of the tree. */
        const TREE_HEIGHT : nat

        /** The values on the left siblings of the path to leaf of index k. */
        var branch : seq<int>

        /** The number of values added to the list. Also the index of the next available leaf.
         */
        var count : nat 

        /** The (Merkle) tree that corresponds to the list of values added so far. */
        ghost var t : Tree<int>

        /** The value of the root of the tree. */
        ghost var r : int

        /** The list of values added so far. */
        ghost var values : seq<int> 

        /** Path to current to the leaf of index count. */
        ghost var p : seq<bit>

        /** The array branch as a sequence. */
        // ghost var left : seq<int>

        //  Properties to maintain

        /** The list of values after count is zero. */
        predicate listIsValid() 
            requires TREE_HEIGHT >= 1
            requires |values| == power2(TREE_HEIGHT - 1)
            reads this
        {
            forall k :: count <= k < |values| ==> values[k] == 0
        }

        /** The tree t is the (Merkle) tree that corresponds to values. */
        predicate treeIsMerkle()
            requires height(t) == TREE_HEIGHT
            requires |values| == |leavesIn(t)|
            reads this
        {
            isCompleteTree(t)
            && isDecoratedWith(diff, t)
            && forall i :: 0 <= i < |values| ==> values[i] == leavesIn(t)[i].v    
            && hasLeavesIndexedFrom(t, 0)
        }

        /** Property to maintain. */
        predicate Valid()
            reads this
        {
            height(t) == TREE_HEIGHT >= 2
            && |values| == power2(TREE_HEIGHT - 1) == |leavesIn(t)|
            && |branch| == TREE_HEIGHT - 1
            && listIsValid()
            && treeIsMerkle()
            && (r == t.v)
            && count < power2(TREE_HEIGHT - 1)
            && p == natToBitList2(count, TREE_HEIGHT - 1)
            && |p| == TREE_HEIGHT - 1
        }

        /**
         *  Initialise the system, tree of size >= 1.
         */
        constructor(h: nat, l : seq<int>, l' : seq<int>, tt: Tree<int>) 
            requires h >= 2
            requires |l| == power2(h - 1) && forall i :: 0 <= i < |l| ==> l[i] == 0
            requires |l'| == h - 1 && forall i :: 0 <= i < |l'| ==> l'[i] == 0
            requires tt == buildMerkle(l, h, diff, 0);
            ensures Valid()
        {
            TREE_HEIGHT := h;
            count := 0;
            //  Initialise array with zeros
            // branch := new int[h](  (x: int) => 0 );
            branch := l';

            //  Initialise ghost variables
            values := l;

            //  possibly left could be left uninitialised
            // left := l';
            t := tt;
            p := natToBitList2(0, h - 1);

            //  Initially r == 0
            r := 0;
            //  Use lemma to prove that r == t.v
            allLeavesZeroImplyAllNodesZero(tt);
        }

        /**
         *  Deposit a value i.e update the state.
         */
        method deposit(value : int) 
            requires Valid()
            requires count < power2(TREE_HEIGHT - 1) - 1

           
            //  requires that branch has the left siblings on current path
            requires  p == natToBitList2(count, TREE_HEIGHT - 1)
            requires // var p := natToBitList2(count, TREE_HEIGHT - 1);
                forall i :: 0 <= i < |p| ==> p[i] == 1 ==> 
                    branch[i] == siblingAt(take(p, i + 1), t).v

            ensures height(t) == TREE_HEIGHT >= 2
                && |values| == power2(TREE_HEIGHT - 1) == |leavesIn(t)|
                && |branch| == TREE_HEIGHT - 1
                && listIsValid()
                && treeIsMerkle()
                // && (count >= 1 ==> r == t.v)
                && count < power2(TREE_HEIGHT - 1) 
                // && (count < power2(TREE_HEIGHT - 1) ==> p == natToBitList2(count, TREE_HEIGHT - 1))

            //  at the end branch has siblings on next p.
            // ensures
            //     forall i :: 0 <= i < |p| ==> p[i] == 1 ==> 
            //         branch[i] == siblingAt(take(p, i + 1), t).v

            ensures p == natToBitList2(count, TREE_HEIGHT - 1)


            modifies this

        {
            ghost var oldCount := count;
            //  The root value computed before update of branch
            ghost var r' := computeRootPathDiffUpv3(TREE_HEIGHT - 1, count, branch, value);
            ghost var leftSiblingsBeforeUpdate := branch; 
            calc ==> {
                forall i :: 0 <= i < |p| ==> p[i] == 1 ==> 
                        branch[i] == siblingAt(take(p, i + 1), t).v;
                forall i :: 0 <= i < |p| ==> p[i] == 1 ==> 
                        leftSiblingsBeforeUpdate[i] == siblingAt(take(p, i + 1), t).v;
            }
            //  Values on the current path with leaf equals to value
            ghost var v1 := computeAllPathDiffUp(p, branch, value);
            //  Prove that v1 contains the values of nodes on p
            assume(forall i :: 0 <= i < |p| ==>           
                            v1[i] == nodeAt(take(p, i + 1), t).v );

            //  Prove pre-conditions for aplying lemma computeLeftSiblingOnNextPathIsCorrect
            calc == {
                bitListToNat(p);
                bitListToNat(natToBitList(count, TREE_HEIGHT - 1));
                { bitToNatToBitsIsIdentity(count, TREE_HEIGHT - 1) ; }
                count;
                <
                power2(TREE_HEIGHT - 1) - 1;
                calc == {
                    TREE_HEIGHT - 1;
                    |p|;
                }
                power2(|p|) - 1;
            }
            pathToNoLasthasZero(p);
            assert(exists i :: 0 <= i < |p| && p[i] == 0 );
            
            //  Compute left sib,ings on next path gives values on the siblings of next path
            computeLeftSiblingOnNextPathIsCorrect(p, t, v1, leftSiblingsBeforeUpdate);
            ghost var siblingsOnNextPath := computeLeftSiblingOnNextPath(p, v1,leftSiblingsBeforeUpdate);
            assert( forall i :: 0 <= i < |p| && nextPath(p)[i] == 1 ==> 
                siblingsOnNextPath[i] == siblingAt(take(nextPath(p), i + 1), t).v);

            //  compute new value for branch
            branch := computeLeftSiblingOnNextPathFinal(TREE_HEIGHT - 1, count, branch, value);
            assert(branch ==  computeLeftSiblingOnNextPath(p, v1, leftSiblingsBeforeUpdate));

            //  Branch contains siblings on next path
            assert( forall i :: 0 <= i < |p| && nextPath(p)[i] == 1 ==> 
                branch[i] == siblingAt(take(nextPath(p), i + 1), t).v);
           
            //  update ghost vars
            values := values[count := value];
            //  Update tree
            t := buildMerkle(values, TREE_HEIGHT, diff, 0);
          
            // assert(r == t.v);

            //  Update count
            count := count + 1;

            p :=  natToBitList2(count, TREE_HEIGHT - 1);
            
            // Prove that p is nextPath(old(p))
            calc ==>  {
                old(p) == natToBitList2(old(count), TREE_HEIGHT - 1);
                { bitToNatToBitsIsIdentity(old(count), TREE_HEIGHT - 1) ; }
                bitListToNat(old(p)) == old(count) ;
            }
            calc ==> {
                p == natToBitList2(count, TREE_HEIGHT - 1);
                { bitToNatToBitsIsIdentity(count, TREE_HEIGHT - 1) ; }
                bitListToNat(p) == count ;       
                bitListToNat(p) == old(count) + 1;
                bitListToNat(p) == bitListToNat(old(p)) + 1;
            }
            isNextPathFromNat(old(p), p);
            assert(p == nextPath(old(p)));

            // calc ==> {

            // }
            
        }

        // in get_deposit_root we shoudl requires that count > 0 otherwise 
        //  no values has been added to the tree
        //  @todo check that the smart contract implem checks before computing 
        //  deposit root

         // var a : array<int>;
        // var branch : array<int>;

        

    }

}