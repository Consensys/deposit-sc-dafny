
[![License](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](https://opensource.org/licenses/Apache-2.0) 
[![made-for-VSCode](https://img.shields.io/badge/Made%20for-VSCode-1f425f.svg)](https://code.visualstudio.com/)
 [![Proofs](https://img.shields.io/badge/ProvedLemmas-136-yellow.svg)](https://shields.io/) 
 [![LoC](https://img.shields.io/badge/LoC-3536-green.svg)](https://shields.io/) 
 [![Checks](https://img.shields.io/badge/DafnyVerify-Verified-orange.svg)](https://shields.io/) 

[![HitCount](http://hits.dwyl.com/https://githubcom/PegaSysEng/eth20-dafny.svg)](http://hits.dwyl.com/https://githubcom/PegaSysEng/deposit-sc-dafny)

# Verification of the Deposit Smart Contract in Dafny

This repository contains the implementation and the formal proof of the Deposit Smart Contract algorithm.

# Breakdown of our results

The source code in this repository is the **first complete formal proof of correctness** of the
incremental Merkle tree algorithm used in the Deposit Smart Contract.
The proofs are designed for an arbitrary attribute of type `T` to be computed on a tree (not restricted to a _hash_ function).
The height of the tree is also parametric and the proof holds for any height.

The proofs and algorithms are written in [Dafny](https://github.com/dafny-lang/dafny/wiki), a verification-friendly programming language.

The main contributions of this project are:

*   a **formal definition** of the correctness criterion,
*   **functional specifications** of correctness,
*   functional and imperative style **algorithms** for the `deposit()` and `get_deposit_root()`.

The main results are:

*   a **fully mechanised proof of correctness* (including termination)
*   a **simplified** version of the `deposit()` algorithm.

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

The Dafny code for `deposit()` (proof and algorithm) can be found [here](https://github.com/PegaSysEng/deposit-sc-dafny/blob/3a57971ae6f9d824647403397734ecbbe7dfe837/src/dafny/smart/DepositSmart.dfy#L186).

# Supplementary Material

*   Some [background information](./wiki//background.md) on Incremental Merkle Tree Algorithm.
*   Some [Statistics](./wiki/stats.md) (number of proofs, LoC, ...)
* A [nice graph](./wiki/structure.svg) of the architecture of this project (self loops indicate recursive functions).

