
[![License](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](https://opensource.org/licenses/Apache-2.0) 
 [![made-for-VSCode](https://img.shields.io/badge/Made%20for-VSCode-1f425f.svg)](https://code.visualstudio.com/)
 [![Proofs](https://img.shields.io/badge/TheoremsProved-132-yellow.svg)](https://shields.io/) 
 [![LoC](https://img.shields.io/badge/LoC-3536-orange.svg)](https://shields.io/) 
 [![Checks](https://img.shields.io/badge/VerificationStatus-Verified-green.svg)](https://shields.io/) 
 [![Hits](https://hits.seeyoufarm.com/api/count/incr/badge.svg?url=https%3A%2F%2Fgithub.com%2FConsenSys%2Fdeposit-sc-dafny&count_bg=%2379C83D&title_bg=%23555555&icon=&icon_color=%23E7E7E7&title=hits&edge_flat=false)](https://hits.seeyoufarm.com)

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
*   a **fully mechanised proof of correctness** (including termination, memory safety and array allocations),
*   **verified algorithms** for the `deposit()` and `get_deposit_root()`
and the initialisation `init_zero_hashes()`.

The main findings are:


*   a proof that the **initial values** in the `branch` array **do not matter** (hence there is no need to initialise it),
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
    branch[i] := root;
    deposit_count := deposit_count + 1;
}
```
Alternatively `deposit_count` can be incremented at the beginning and in that case the `while` loop condition
is negated `size % 2 == 0`.

Note that our proofs include **memory safety** and we have verified that:
1. arrays (`branch` and `zero_hashes`) are properly referenced,
2. there is **no** side-effects on `zero_hashes` when updating an element in `branch`,

We have also proved the `zero_hashes` initialisation algorithm. 

The memory safety proofs use Dafny _dynamic framing_ features and the `{:autocontracts}` annotation for the deposit contract class. 

The Dafny code for `deposit()` (proof and algorithm) can be found [here](https://github.com/ConsenSys/deposit-sc-dafny/blob/master/src/dafny/smart/DepositSmart.dfy).

# Overview

Most of the code in this repository pertains to the **correctness** proofs of the algorithms.
The _proof_ code is a Dafny program but does not need to be executable (e.g. we use `function` or `lemma` 
to write the proofs rather `method` or `function method` to write executable code).
The core algorithms for the incremental Merkle tree algorithms (imperative and functional styles) are very short (see  the _algorithms_ directory 
[Statistics](./wiki/stats.md)).

The Deposit Smart Contract code and its correctness proof in [DepositSmart.dfy](https://github.com/ConsenSys/deposit-sc-dafny/blob/master/src/dafny/smart/DepositSmart.dfy) relies on several auxiliary proofs with functions and lemmas.
The code for these proofs has not been _optimised_ and some of the hints provided in the proof code are not necessary for Dafny
to prove the results. 

The proof of the algorithm follows a principled approach to algorithm design: 
* some **key properties** of the problem are identified,
* a **logical correctness criterion** is defined using Merkle trees,
* **functional style algorithms** are designed and **proved correct** with respect to the correctness criterion,
* the **imperative versions** (with `while` loops) are **proved correct** by showing that they compute the
same result as the functional algorithms,
* **memory safety** (and dynamic array allocation) is addressed using _dynamic framing_ supported by Dafny,

This technique has the advantage of highlighting the main steps of the proof:
* the incremental Merkle tree efficient algorithm is an instance of **dynamic programming**,
* the correctness proofs are provided on the **functional style versions first**. It is easier to prove correctness on the side-effect free algorithms. 
The final step of proving that the imperative versions of the algorithms are correct boils down to proving that they compute the same result
as their functional counter-parts and is somehow detached from the intricacy of the correctness proofs.

# Problem Statement and Proof

The following sections may help the reader understand the idea of the proof and how it is implemented in Dafny:

 * Some [background](./wiki//background.md) on the Incremental Merkle Tree problem and algorithm.
 * The main [proof ideas and sketch](./wiki/sketch.md).
 * The [correctness criterion](./wiki/correctness.md).  
 * The `deposit()` and `get_deposit_root()` [algorithms](./wiki/algos.md). 


# Repeatability of Results

We provide a Docker container to run the verification with Dafny.

All the files can be checked using the following command assuming `dafny` is the Dafny executable:
```bash
dafny /dafnyVerify:1 /compile:0 /tracePOs /traceTimes /noCheating:1 file.dfy
```
The `/noCheating:1` ensures that  `assume` statements (if any) are treated as _untrusted_ and 
processed by the verifier as claim to prove rather than `assume`, i.e. they are replaced by  `assert`. 

> The time it takes to verify the proofs depend on the computer, and OS. 
> As a result it may happen that the analysis is inconclusive (times out) with the Dafny 
> default command line flags. We provide a shell script that runs the verification
> for each directory/file with dafny command line arguments that should be suitable for the 
> analysis to run to completion (see [check the proofs](./wiki/repeatability.md)). 


To install and run the full verification you may refer to the following:
* the steps to [check the proofs](./wiki/repeatability.md),
* some references if you choose to [install dafny](./wiki/dafny-install.md).

  

# Supplementary Material

The following resources provide a high-level picture of the code:

* [Statistics](./wiki/stats.md) (number of proofs, LoC, ...)
* A [nice dependency or call graph](./wiki/structure.svg) tha depecits the architecture of this project (self loops indicate recursive functions).

