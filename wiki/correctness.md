
[ [up] ](../README.md) 

# Correctness criterion

In this section we describe the correctness criterion we use to prove correctness.
 
In the previous sections [background](background.md) and [sketch](sketch.md) we have proposed recursive (functional) algorithms to define the `deposit()` and `get_deposit_root()` functions. 

In this section we explain how we can prove that the imperative versions used in the deposit smart contract are correct.

## Correctness
We assume a given fixed height >= 1 for the tree.

The Deposit Smart Contract behaviour should correspond to incrementally building a Merkle tree that records the values inserted so far
and retrieving the correct value for the root hash.
On a time line, the initial tree corresponds to an empty list of inserted values: it is denoted `T([])` in the [background](./background.md) section.
After `n` insertions the list of inserted values is `v1::v2::...::vn` and the corresponding Merkle tree is
`T(v1::v2::...::vn)`.


The _visible_ and desirable behaviour of the `deposit()` and `get_deposit_root()` functions, which is the **correctness criterion** should be as follows:
1. if `deposit()` is called `n` times with the sequence of values `v1, v2, ..., vn`, i.e. we successively execute
    `deposit(v1)`, `deposit(v2)`, ..., `deposit(vn)`, 
2. then if we call `get_deposit_root()` the value that should be returned is `T(v1::v2::...::vn).v` which is the value
    of the _hash_ attribute on the root of the tree `T(v1::v2::...::vn)`.

Of course the main feature of the functions `deposit()` and `get_deposit_root()` is that they should do so while **avoiding to actually maintain a full representation of the tree** and this is why we use the term _visible_ behaviour above.

However, the correctness criterion requires that we model the tree that would be obtained after the `n` insertions. 

This is why a substantial part of the source code (including the `tree` folder) is devoted to the **Tree** data-structures and theorems, although this is used only for verification purposes.

Our correctness proof relies on two main properties of `deposit()` and `get_deposit_root()`:


0. assume we have inserted a list `l` of `n >= 0` values i.e. called `deposit()` `n` times with a list `l` of `n` values, 
1. assume the `branch` vector contains the values of the left siblings of the path the (n + 1)-th leaf, indexed `n`, in the tree `T(l)`,
2. **Theorem 1**: after executing `deposit(v)`, `branch` contains the values of the left siblings of the path
    to the (n + 2)-nd leaf at index `n + 1` in the tree `T(l :: v)`.
2. **Theorem 2**: given `branch` the values on the left siblings of the path to the (n + 1)-th leaf indexed `n`, `get_deposit_root()`   returns the value of  `T(l :: v)`.

**Theorem 2** can be proved using the assumption on `branch`.
**Theorem 1** is proved by induction on the length of the list of inserted values. In Dafny it is proved by showing that a property
called `Valid()` is an inductive invariant.

The [inductive invariant](https://github.com/PegaSysEng/deposit-sc-dafny/blob/e4de78df6636652ba8f4a2b270c7649904866594/src/dafny/smart/DepositSmart.dfy#L83) is defined by:
```dafny
predicate Valid()
    reads this
{
    //  Constraints on height and length of lists.
    1 <= TREE_HEIGHT == |branch| == |zero_h| 
    //  Maximum number of values stored in the tree bounded.
    && count < power2(TREE_HEIGHT) 
    //  count is the number of values added so far and should correspond to |values|.
    && |values| == count
    //  zero_h is constant and equal to default values for each level of t.
    && zero_h == zeroes(f, d, TREE_HEIGHT - 1)
    //  branch and zero_h are the left and right siblings of path to 
    //  |values|-th leaf in buildMerkle(values, TREE_HEIGHT, f, d)
    && areSiblingsAtIndex(|values|, buildMerkle(values, TREE_HEIGHT, f, d), branch, zero_h)
}
```
where the last line encodes the desired property: 

* `values` is tracking the list of values inserted so far (it is a `ghost` variable in Dafny), 
* and `branch` and `zero_h` should contain the values of the siblings (predicate `areSiblingsAtIndex`) 
of the path to the leaf indexed `|values|` (length of values) in the tree that corresponds to `values` (`buildMerkle(values, TREE_HEIGHT, f, d))` with `f` the attribute to compute and `d` the default values).

<!-- ## Merkle Trees -->



## Pre and Post-conditions

The [proof of **Theorem 2**](https://github.com/PegaSysEng/deposit-sc-dafny/blob/e4de78df6636652ba8f4a2b270c7649904866594/src/dafny/smart/DepositSmart.dfy#L298) is encoded as a pre/post-conditions for the `get_deposit_root()` function:

```dafny
 method get_deposit_root() returns (r : int) 
    requires Valid()    //  assume Theorem 1 holds before the call
    ensures Valid()     //  ensures Theorem 1 still holds after the call
    /** Ensures the result r of get_deposit_root_() is the root value of the Merkle tree for values.  */
    ensures r == buildMerkle(values, TREE_HEIGHT, f, d).v 
{
    ...
}
```
The post-conditions ensure:

1. that `Valid()` is preserved,
2. the value that is returned at any point in time is the value that the root of the Merkle tree for `values` would have.
To prove this Theorem, the source code of `get_deposit_root()` must be annotated by some
loop invariants (properties) that are automatically checked by Dafny.

The invariant-annotated source code for this function is [here](https://github.com/PegaSysEng/deposit-sc-dafny/blob/ee2710bfc88dc60777031ec1a6d18ab11f32a571/src/dafny/smart/DepositSmart.dfy#L298).

The [proof of **Theorem 1**](https://github.com/PegaSysEng/deposit-sc-dafny/blob/e4de78df6636652ba8f4a2b270c7649904866594/src/dafny/smart/DepositSmart.dfy#L188) amounts to showing that `Valid` is preserved (note that in our code `branch` is stored in reverse order
compared to the original algorithm and we use index `TREE_HEIGHT - i - 1` instead of `i`):
```dafny
method  deposit(v : int) 
    requires Valid()
    requires count < power2(TREE_HEIGHT) - 1   //   tree is not full 
    ensures Valid()
{
    //  deposit algorithm
    var value := v;
    var size : nat := count;
    var i : nat := 0;
    while size % 2 == 1 {
        value := f(branch[TREE_HEIGHT - i - 1], value);
        size := size / 2;
        i := i + 1;
    }
    branch := branch[TREE_HEIGHT - i - 1 := value];
    count := count + 1;

    //  Update of the list of values inserted so far
    values := values + [v];

    //  proof 
    ...
}
```
The proof if this property requires the annotation of the source code with loop invariants
that can be checked by Dafny.
The -annotated source code for this function is [here](https://github.com/PegaSysEng/deposit-sc-dafny/blob/ee2710bfc88dc60777031ec1a6d18ab11f32a571/src/dafny/smart/DepositSmart.dfy#L188).

[ [up] ](../README.md) 
