
[ [up] ](../README.md) 

# Sketch of the proof

If not familiar with the incremental Merkle tree problem (and algorithms) you may start with the [background section](./background.md) 
for a quick introduction to the problem. 
In this section, without loss of generality,  we use a simple attribute `diff` instead of the _hash_ function in Merkle trees.  

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
leaf at the end of `p`, we can recursively compute the new root as follows:

```dafny
function computeRootUp(p : seq<bit>, s: seq<int>, seed: int) : int
    requires |p| == |s|
    decreases p
{
    if |p| == 0 then
        seed 
    else 
        var x := if last(p) == 0 then diff(seed, last(s)) else diff(last(s), seed);
        computeRootUp(init(p), init(s), x)
}
```
and if we split the siblings's values `s` into two vectors `b` and `z` for the left and right siblings:
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
the siblings of the nodes on the path to the next available leaf in the tree.


## Computing the left siblings of the next path