
# Verification of the Deposit Smart Contract in Dafny

This repository contains the implementation and the formal proof of the Deposit Smart Contract algorithm.

# Breakdown of our results

The source code in this repository is the first complete formal proof of correctness of the
incremental Merkle tree algorithm used in the Deposit Smart Contract.
The proofs are designed for an arbitrary attribute of type `T` to be computed on a tree (not restricted to a _hash_ function).
The height of the tree is also parametric and the proof holds for any height.

The proofs and algorithms are written in Dafny, a verification-friendly programming language.

The main contributions of this project are:

*   a _formal definition_ of the correctness criterion,
*   _functional specifications_ of correctness,
*   functional and imperative style algorithms for the `deposit()` and `get_deposit_root()`.

The main results are:

*   a complete proof of correctness (including termination)
*   a simplified version of the `deposit()` algorithm.

The **provably correct** simplified version of `deposit()` is as follows:

```dafny
method deposit(v : int) 
    requires deposit_count < power2(TREE_HEIGHT) - 1 
{   
    var root := v;
    var size : nat := deposit_count;
    var i : nat := 0;
    
    while size % 2 == 1 {
        root := hash(branch[i], root);
        size := size / 2;
        i := i + 1;
    } 
    //  i is guaranteed to satisfy 0 <= i < TREE_HEIGHT 
    //  This ensures the absence of out of bounds error in the following update 
    branch[i] := := root;
    deposit_count := deposit_count + 1;
}
```
Alternatively `deposit_count` can be incremented at the beginning and in that case the `while` loop condition
is negated `size % 2 == 0`.

The Dafny code (proof and algorithm) can be found [here](https://github.com/PegaSysEng/deposit-sc-dafny/blob/3a57971ae6f9d824647403397734ecbbe7dfe837/src/dafny/smart/DepositSmart.dfy#L186).

# Supplementary Material

*   Some [background information](./wiki//background.md) on Incremental Merkle Tree Algorithm.
*   Some [Statistics](./wiki/stats.md) (number of proofs, LoC, ...)
* A [nice graph](./wiki/structure.svg) of the architecture of this project (self loops indicate recursive functions).

