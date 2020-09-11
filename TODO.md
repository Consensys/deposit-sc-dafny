TODO

1. seq<bit> stuff in module [DONE]
2. seqHelpers in module [DONE]
3. clean up all the fooxx (and maybe remove unused ones)
4. add proof that left siblingsAt(nextPath(p)) are in p or in left siblings of p  [DONE]

5. merge computeLeftSiblingOnNextPath and computeRootPathDiff
6. prove that it maintains an invariant (including starting from empty tree).


check files and add comments, polish proofs!

restore index in leaves to make sure they are unique. [DONE]

1. finish proof of equiv v1 and v2 [DONE]
2. add computeRootPathDiffUp returning the sequence of values [DONE]
3. show that v1 (with this computeRootDiffUp) is correct [DONE]

4. preserve values in left siblings values  
    a. whenever possible return old left value rather than "seed" [DONE]
    b. lift proof of correctness [DONE]


6.  imperative version of algorithm
    a. use 2 arrays and write a method?
    b. use one array to update in-place.

7. Simplify (if possible) nextPathInCompleteTrees [DONE]

8. prove that MerkleV1 satisfies correctness V4c
    a. Fix requires == h - 1 in correctness proof.
    b. use lemma in proof of MerkleV1

5. show correctness with functional version
    a. without optimisation
    b. with optimisation: switch to compteRootPathUp (no left siblings value) when k % 2 == 0


a. integrate constraint the branch is values on left sibling of current compteRootPath
b. use lemma (where?) to prove that in this case computeRootPathUp gives the root value
c. use lemma commute to prove that deposit correctly update state to compute root value.

%-----------------------------------------------------------------------------------------------


