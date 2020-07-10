
# deposit-sc-dafny

Deposit smart contract in Dafny

# Incremental Merkle Tree Algorithm

The core component of the Deposit Smart Contract is the so-called _Incremental Merkle Tree_ algorithm.

Given a tree **T**, the _Merkle Tree_ that corresponds to **T** is a (binary complete) tree decorated with some _attribute_ (values attached to the nodes).
Computing the attribute for all the nodes of a tree requires to walk the tree and to explore all the nodes, for instance using a Depth First Traversal algorithm. 

In the context of a Blockchain, a Merkle tree may be used to store elements of a list **L**. The value of the attribute (the _hash_) on the tree root can be used to test membership of an element in the list. The is known as a Merkle Proof. We are not concerned with Merkle Proofs in this project but rather in computing the _hash_ attribute on a tree that stores elements of a list.

By Merkle tree, we mean a binary complete tree decorated with the Merkle attribute (_hash_).

A Merkle tree of height **h** is a _binary_ and _complete_ tree, meaning that 1) every node that is not a leaf has two children and 2) all the branches of the tree from the root to the leaves have the same height **h**. 
The leaves of a Merkle tree contains the elements of a list **L** from left to right.
Again, these elements are organised as a binary tree in order to define a property, the _hash_  of the list **L**, as an attribute on the tree representation of **L**. 

A Merkle tree of height **h** is a binary complete tree and this entails: 1) the number of nodes in the tree is **2^(h) - 1** and 2) the number of leaves is **2^(h - 1)**.
It follows that Merkle trees of height **h** can represent lists of at most **2^(h - 1)** elements.

To represent a list of **n < 2^(h - 1)** elements with a binary complete tree of height **h**,
 **L** is right-padded with  dummy or neutral elements (e.g. zeroes) to obtain **L'** of length **2^(h - 1)**. **L'** is used to define the leaves of a complete binary tree, on which the Merkle attribute (_hash_) can be computed.

The incremental Merkle tree problem is infornally: how to _incrementally_ (and efficiently) compute the Merkle attribute on binary complete trees for lists that grow monotonically such as <math>L</math>, <math>L + e1</math>, <math>(L + e_1) + e_2 ]</math> (where _+_ is the append operator) and so on.


More precisely, the problem of interest can be  stated as follows: 

**IncMerkleTree** Problem:
**given** 1) a Merkle tree of height **h**,  **MKL(L)**, that stores a list **L** that has less than **2^(h -1)** elements, and 2) an element **e**,  can we efficiently compute (without traversing the the **2^h - 1** nodes of the tree)  **MKL(L + e)**?

To solve the previous problem, it may be useful to recall some simple definitions and algorithms to identify similarities with knowm problems and also the key issues that we have to address to solve **IncMerkleTree**. In this context, computing attributes on trees seems to be relevant and this is the topic of the next section.

# Computing Attributes on Tree Structures

## Binary Trees

A binary tree can be defined by an Abstract Data Type (ADT) as follows:

```haskell
datatype Node = 
            Leaf
        |   Node(left: Node, right: Node)
```

A node is either a leaf or an internal node with two (ordered) children, _left_ and _right_.
This ADT is enough to represent binary trees, as a binary tree is fully determined by its _root_ which is a node (including trees with single node-leaf).
This definition does not allow empty trees.

## Synthesised Attributes

The Merkle attribute belongs to the category of _synthesised_ attributes.
A _synthesised attribute_ on a tree is **defined** bottom-up: the values of the decorations are given on the leaves, and to compute the values on the internal nodes, the values of the left and right children are needed. 

A simple example of a _synthesised attribute_ is the _height_ of a tree that can be defined by:

```haskell
function height(root : Node) : nat 
  {
    match root 
     //  a tree which is a leaf has height 1
     case Leaf => 1
     //  The height of a tree with children is 1 + the max size of the children
     case Node(lc, rc) => 1 + max(height(lc), height(rc))
  }
```

## Computing Synthesised Attributes
To store the value of an attribute of type _T_ we can use a _generic_ version of the ADT for binary tree:

```haskell
datatype Node<T> = 
            Leaf(v: T)
        |   Node(v: T, left: Node, right: Node)
```

For instance, `Node<int>` can store the value of non-negative integers attribute like `height`.

The height attribute is a simple one. To define a problem that is equivalent to the **IncMerkleTree** problem, we may use a synthesised attribute that is _assymetric_.
A simple version is to assume that each leave holds an _integer_ value, and the value of an internal node is the difference between the values of the left and right children.

To check that an `int`-decorated tree stores the value of the previous attribute, we can write the following predicate: 

```haskell
predicate isDecoratedWithDiff(root: Node<int>)
{
    match root
        case Leaf(v) => true

        case Node(v, lc, rc) => v == diff(lc.v, rc.v)
}
```

