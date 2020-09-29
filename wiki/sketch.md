
[ [up] ](../README.md) 

# Sketch of the proof

If not familiar with the incremental Merkle tree problem (and algorithms) you may start with the [background section](./background.md) 
for a quick introduction to the problem. 

In this section, without loss of generality,  

> we use a simple attribute `diff` instead of the _hash_ function in Merkle trees.  
> we assume that the trees we mentioned in the sequel are all binary and complete trees.


## Computing the root value of a Merkle tree

<center>
<figure>
<img src="computeRoot1.jpg" alt="Impact of leaf change" width="600">
<figcaption><strong>Figure 1</strong>: The root value can be computed on the green path using the new inserted value (4), the values on the left siblings of the path (yellow) and right siblings (purple). </figcaption>
</figure>  
</center>

When a new value (e.g. `4`) is inserted in the tree, the root value for the attribute `diff(x, y) = x - y - 1` 
can be computed as follows:

* the **green path** leads to the leaf where the new value `4` is inserted,
* assume we have the **values of the attribute `diff`** on the **left** (yellow) and **right** (purple) **siblings** for each node on the green path.
* we can compute the new root value given by `diff` by **walking up** the green path in the tree.   

If we denote by `n.v` the value of `diff` on a node of the tree, the computation runs as follows walking up each level of the tree:

0. `n5.v = 4` (inserted value) and `n6.v = 0` (default value).
1. `n11.v = diff(n5.v, n6.v) = 3`
2. `n14.v = diff(n.11.v, n12.v) = diff(3, -1) = 3`
3. `n15.v = diff(n13.v, n14.v) = diff(-7, 3) = -11`. 

Assume we have a vector `s` that  stores the values of the siblings at each **level** of the tree.
For instance we can have `s = [-7, -1, 0]` that holds the values of the siblings (`n13`, `n12`, `n6`) of the nodes 
on the green path, from top to bottom.

To decide how to combine the values at each level when walking up the green path, 
we need to know whether we are on a _left_ or _right_ child of a node.
To do so, we can encode the green path as a sequence of _bits_ `0` or `1`. In this example  the green path is encoded
as `[1, 0, 0]` (green boxes in **Figure 1**): from the root node to the leaf, go right (1), and twice left (0). 

Given a list or a sequence `x` of length >= 1, we denote:
* `last(x)` the last element of the list, e.g. `last([1, 0, 2]) = 2`,
* `init(x)` the _initial prefix_ of `x` i.e. the list minus its last element,   e.g. `init([1, 0, 2]) = [1, 0]`.

Given `s`, `p` (the sequence of bits encoding the path from the root to the newly inserted leaf) and the value `seed` inserted at the
leaf (at the end of `p`), we can recursively compute the new root as follows:

```dafny
function computeRootUp(p : seq<bit>, s: seq<int>, seed: int) : int
    requires |p| == |s|
    decreases p
{
    if |p| == 0 then
        //  We are at the root and seed contains the value of the attribute for this node.
        seed 
    else 
        //  Decide how to compute the value at the bottom level (last(p)) 
        //  based on direction of path 0 (left) or 1 (right) at last(p)
        var x := if last(p) == 0 then diff(seed, last(s)) else diff(last(s), seed);
        //  Use x as the new seed on the initial prefix of the path (bubble up)
        computeRootUp(init(p), init(s), x)
}
```
And if we split the siblings's values `s` into two vectors `b` and `z` for the left and right siblings:
```dafny
function computeRootLeftRightUp(p : seq<bit>, b: seq<int>, z: seq<int>, seed: int) : int
    requires |p| == |b| == |z|
    decreases p
{
    if |p| == 0 then
        seed 
    else 
        var x := if last(p) == 0 then diff(seed, last(z)) else diff(last(b), seed);
        computeLeftRightRootUp(init(p), init(b), init(z), x)
}
```
This is it.

The `get_deposit_root()` function in the Deposit Smart Contract makes use of a neat trick: the insertion of a new value in the tree
is handled by a function `deposit()` that makes sure the two vectors `b` and `z` hold the values on the left and right siblings for the path to the leaf that is **next** to the leaf where the last value was inserted (see **Figure 2**).  
<center>
<figure>
<img src="computeRoot2.jpg" alt="Impact of leaf change" width="600">
<figcaption><strong>Figure 2</strong>: 'b` and `z` hold the values of the left and right siblings for the path to the next
leaf. </figcaption>
</figure>
</center>

As a consequence, the root value can be computed **without the knowledge of the last inserted value** using the default value (0) as the seed.  
The (tail recursive) functional version of the algorithm for computing the root value is:
```dafny
function get_deposit_root(p : seq<bit>, b: seq<int>, z: seq<int>) : int
    requires |p| == |b| == |z|
    decreases p
{
    if |p| == 0 then
        0 
    else 
        var x := if last(p) == 0 then diff(seed, last(z)) else diff(last(b), seed);
        get_deposit_root(init(p), init(b), init(z), x)
}
```

The next section explains how to maintain the values of `b` and `z` to ensure they store the values of
the siblings of the nodes on the path to the next available leaf in the tree (blue path in **Figure 2**).


## Computing the left siblings of the next path

In this section we highlight a surprising result: to update the values of left siblings when a new value is inserted,
we need to perform a single update to the vector `b`.
Indeed, the right siblings are constant (depending on each level) and we do not need to update them.

We will explain how to maintain the values of the left siblings of a path in phases and address the following
issues:

1. given a path to a leaf, what is the **encoding (list of bits) of the next path**, `nextpath(p)` ?
2. if we are **given the values of `diff` on a path `p` and the left siblings `p`**, can we compute 
    the **values of the left siblings on** `nextPath(p)`?
3. if we are **given the value to insert** at the of the current path `p` (and the left siblings of `p`), can we compute
 the **values of the left siblings on** `nextPath(p)`?

The next section address these issues.

### The next path

in this section we address the following problem:
 
> Given a path to a leaf, what is the **encoding (list of bits) of the next path**, `nextpath(p)` ?

The leaves of a complete binary tree of height `h` are indexed from left (index `0`) to right `index power2(h) - 1` (see **Figure 3**). 
Given a path `p` to the `k`-th  with `k < power2(h) - 1` (i.e not the last leaf), 
the _next path_ of `p`  is the path to the `k + 1`-th leaf.

<center>
<figure>
<img src="nextPath1.jpg" alt="Next path 1" width="600">
<figcaption><strong>Figure 3</strong>: The next path of a path to <strong>left</strong> leaf. </figcaption>
</figure>
</center>

As mentioned before a path in a complete tree of height `h` can be encoded as a sequence of `h` bits.
**Figure 3** shows a green path `green = [0, 1, 0]` leading to the leaf indexed `3`.
The next path of `green` is `blue == [0, 1, 1]`. 
It is easy to compute the path to the next leaf when a leaf is a left child: we just replace the trailing zero in `p` with
a `1`.

When `p` leads to a right child as `green` in **Figure 4** (below) the next path of `green` is slighly more complicated to compute:
we have to go up the `green` path until we hit a node coming from the left child and then we swap.
In other words, we go up the `green` path and process the bit encoding of `green` form 
last to first to build `nextPath(green)` as follows:
 * if the current bit is a `1` we replace it with `0`,
 * if the current bit is `0` we flip it to a `1`.
 * after flipping to `1` we leave the bits unchanged.  

<center>
<figure>
<img src="nextPath2.jpg" alt="Next path 1" width="600">
<figcaption><strong>Figure 4</strong>: The next path of a path to <strong>right</strong> leaf. </figcaption>
</figure>
</center>

As it turns out, we can write the bit encoding of `green` in the form `init :: 0 :: ones(n)` where `ones(n)`, 
`n >= 0` is the list of `n` `1`'s (empty for `n = 0`.)
And `nextpath(green)` is `init :: 1 :: zeroes(n)` where `zeroes` is `n` zeroes.

The generalisation to arbitrary path follows: given `p` of the form `p = init :: 0 :: ones(n)`, `nextPath(p) = init :: 1 :: zeroes(n)`. 
`nextpath(p)` can be broken down into three components as depicted in **Figure 4**: the common  prefix `init` between `p` and 
`nextpath(p)`, the flipped bit, and the _mirrored_ tail of ones.

A few remarks are in order to make sure the previous algorithm is correct:
1. if a path `p` leads to a leaf that is **not the last one**, it **must have a zero** somewhere in its bit encoding.
2. the computation of the encoding of `nextpath(p)`, say `0b.nextpath(p)`, can be obtained by adding `1` in binary to the
encoding of `p`, i.e. `0b.nextpath(p) = 0b.p + 0b1`.

The following algorithm computes the encoding of the next path of `p`:
```dafny
function nextPath(p : seq<bit>) : seq<bit> 
    /** Path has at least on element. */
    requires |p| >= 1
    /** Not the path 1+ that has no successors. */
    requires exists i :: 0 <= i < |p| && p[i] == 0
    ensures |nextPath(p)| == |p|

    decreases p
{
    if last(p) == 0 then 
        init(p) + [1]
    else 
        nextPath(init(p)) + [0]
}
```

The Dafny source code for operations on path as sequences of bits is [SeqOfBits.dfy](https://github.com/PegaSysEng/deposit-sc-dafny/blob/master/src/dafny/smart/seqofbits/SeqOfBits.dfy).
Note that we do not need to compute or execute the `nextPath` function so we do not need to make it tail recursive.

### Computing the values of the siblings on the next path 

In this section we address the following problem:

> If we are **given the values of `diff` on a path `p` and on the left siblings of `p`**, can we compute 
>    the **values of the left siblings on** `nextPath(p)`?

Now that we have seen what `nextPath(p)` is compared to `p`, we can convince ourselves that the answer to this question is: yes.
Or almost.

**Figure 5** illustrates how we can solve this problem.
Assume we have the values of nodes on the `green` path after a new value (`5`) is inserted at the end of `green`.
The values appear in purple on the nodes of the `green` path and to compute them we used the values of the left (yellow) 
and right (orange) siblings of the nodes on the `green` path.

<center>
<figure>
<img src="nextPath3.jpg" alt="Next path 3" width="600">
<figcaption><strong>Figure 5</strong>: The left siblings of next path. `blue` path is `nextpath(green)` </figcaption>
</figure>
</center>

Let `b` be the values of the left siblings on the `green` path with `b = [-7, - , 4]`: `b[0]` is the left sibling for node `n14` (root),
`b[1]` is not relevant aa the sibling at `n13` is on the right, and `b[2]` is the left sibling for node `n10`. 

We want to compute `b'` which hold the values of the left siblings for `nextPath(p)`.
We know that if `p` is of the form `p = init :: 0 :: ones(n)`, then `nextPath(p) = init :: 1 :: zeroes(n)`.
It follows that on the suffix `zeroes(n)` of `nextPath(p)` all the values we need are from **right siblings** 
(the values of which is determined by the current height in the tree). 
As a result the last `n` values of `b'` are irrelevant as at the corresponding levels in the tree the nodes are right siblings.
Moreover, `p` and `nextpath(p)` share the initial prefix prefix `init` and thus share the same initial prefix of left siblings.
If `init` has length `m`, then `b'[0..m - 1] = b[0..m -1]`.
The only unknown for `b'` is the value of the left sibling at level `m`.
For example in **Figure 6**, node `n13` is where the next path of `green` forks from `green`.
And at this level, the value of the left sibling of `n11` is the value at `n10` which is known as it is on the `green` path.

Computing the value of the siblings on `nextPath(green)` `b'` can be done using the values of the left siblings of `green` (in `b`) and the values on `green` say in `v1`
as follows:
1. `b' := b`; the initial prefix  `b'[0..m - 1]` is the same as `b[0..m -1]` and the suffix after `m` is irrelant so we can
 use the old values in `b`.
2. `b'[m] := v1[m]`, this is only update that is needed to obtain the values of the left siblings on the next path.

The following algorithm computes the values of left siblings of `nextPath(p)` given the value son the left siblings of `p` and
the values on `p` (`first(p)` denotes the first element of the list `p`):

```dafny
function method computeLeftSiblingOnNextPath<T>(p: seq<bit>, v1 : seq<T>, left : seq<T>) : seq<T>
    requires 1 <= |p| 
    requires |v1| == |left| == |p|
    ensures |computeLeftSiblingOnNextPath(p, v1, left)| == |v1|

    decreases p
{
    if |p| == 1 then
       /*  If p[0] == 0, we use the value on the path i.e v1, and otherwise p[0] == 1 we can choose
        *  whatever we want as at this level as the sibling on the next path is on is right siblings
        *  We choose to use left i.e. keep the same value for sibling at this level,  in order to
        *  enable optimisations in the imperative version of the algorithm where a single array is used.
        */
        if first(p) == 0 then v1 else left 
    else 
        assert(|p| >= 2);
        if last(p) == 0 then 
           /*  This is where the next path flips side. The next path is of the form init(p) + [1].
            *  The prefix of p and of nextPath(p) share the same siblings, and the the left sibling 
            *  on nextPath at this level is the elft child, so we use its value [last(v1)].
            */
            init(left) + [last(v1)]
        else 
            assert(last(p) == 1);
            /*  The nextPath is of the form nextPath(init(p)) + [0].
             *  So the sibling at this level is a right sibling and the value we store in the
             *  result for this result is irrelevant. We choose to keep the value of the previous left
             *  sibling from left in order to allow optimisations in the impertive version of the algorithm.
             */
            computeLeftSiblingOnNextPath(init(p), init(v1), init(left)) + [last(left)]
} 
```

### Computing the values of the siblings of next path after inserting a new value in the tree

The `deposit()` function in the Deposit Smart Contract performs the computation of the values on `p` at the same time as it compute the values of the left siblings on `nextpath(p)` using the inserted value `seed` and the default values on the right siblings of `p`: 

```dafny
function method computeLeftSiblingOnNextPathFromLeftRight(p: seq<bit>, left : seq<int>, right : seq<int>, seed : int) : seq<int>
    requires 1 <= |p| 
    requires |left| == |right| == |p|

    decreases p
{
    if |p| == 1 then
        if first(p) == 0 then [seed] else left 
    else 
        assert(|p| >= 2);
        if last(p) == 0 then 
            init(left) + [seed]
        else 
            assert(last(p) == 1);
            computeLeftSiblingOnNextPathFromLeftRight(init(p), init(left), init(right), diff(last(left), seed)) 
            + [last(left)]
} 
```

To summarise, we have designed the function `computeLeftSiblingOnNextPathFromLeftRight` to compute the left siblings on the next path, given the left siblings on the previous path, the default valus for right siblings, and the value to insert.