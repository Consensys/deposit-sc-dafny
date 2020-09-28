
[ [up] ](../README.md) [ [next] ](./structure.svg)

# Source Code Statistics

In the table below the columns represent:

*  **Files/Folder**: the file name and the directory it can be found in.
*  **#LoC** is the number of lines of code in the file (excluding white spaces and comments).
*  **Lemmas** is the number of lemmas proved in the file.
*  **Implementations** is the number of implementations with pre/post conditions proved in the file.
* **Documentation** is the number of lines of documentation (JavaDoc style).
* **#Doc/#LoC (%)** is the ratio of documentation vs LoC.
* **Proved** is the number of lemmas and implementations proved in the file.


|    | Files                             | Folder                         |   #LoC |   Lemmas |   Implementations |   Documentation |   #Doc/#LoC (%) |   Proved |
|----|-----------------------------------|--------------------------------|--------|------------|-------------------|-----------------|-----------------|----------|
|  0 | DepositSmart.dfy                  | src/dafny/smart                |    163 |          0 |                 5 |              90 |              55 |        5 |
|  1 | CommuteProof.dfy                  | src/dafny/smart/algorithms     |     73 |          2 |                 0 |              31 |              42 |        2 |
|  2 | IndexBasedAlgorithm.dfy           | src/dafny/smart/algorithms     |     96 |          3 |                 2 |              59 |              61 |        5 |
|  3 | MainAlgorithm.dfy                 | src/dafny/smart/algorithms     |     66 |          2 |                 0 |              38 |              58 |        2 |
|  4 | OptimalAlgorithm.dfy              | src/dafny/smart/algorithms     |     24 |          2 |                 0 |              15 |              62 |        2 |
|  5 | Helpers.dfy                       | src/dafny/smart/helpers        |     51 |          5 |                 1 |              10 |              20 |        6 |
|  6 | SeqHelpers.dfy                    | src/dafny/smart/helpers        |    137 |         10 |                 6 |              34 |              25 |       16 |
|  7 | NextPathInCompleteTreesLemmas.dfy | src/dafny/smart/paths          |    262 |          3 |                 2 |              99 |              38 |        5 |
|  8 | PathInCompleteTrees.dfy           | src/dafny/smart/paths          |    408 |         15 |                 0 |              60 |              15 |       15 |
|  9 | SeqOfBits.dfy                     | src/dafny/smart/seqofbits      |    527 |         19 |                 0 |             100 |              19 |       19 |
| 10 | ComputeRootPath.dfy               | src/dafny/smart/synthattribute |    305 |         11 |                 0 |             116 |              38 |       11 |
| 11 | GenericComputation.dfy            | src/dafny/smart/synthattribute |    148 |          6 |                 0 |              75 |              51 |        6 |
| 12 | RightSiblings.dfy                 | src/dafny/smart/synthattribute |    210 |          5 |                 1 |              57 |              27 |        6 |
| 13 | Siblings.dfy                      | src/dafny/smart/synthattribute |    124 |          2 |                 0 |              31 |              25 |        2 |
| 14 | SiblingsPlus.dfy                  | src/dafny/smart/synthattribute |    556 |          4 |                 0 |              52 |               9 |        4 |
| 15 | CompleteTrees.dfy                 | src/dafny/smart/trees          |     89 |          8 |                 1 |              19 |              21 |        9 |
| 16 | MerkleTrees.dfy                   | src/dafny/smart/trees          |    208 |          6 |                 3 |             101 |              49 |        9 |
| 17 | Trees.dfy                         | src/dafny/smart/trees          |     91 |          3 |                 5 |              41 |              45 |        8 |
| 18 |                                   | TOTAL                          |   3538 |        106 |                26 |            1028 |              29 |      132 |