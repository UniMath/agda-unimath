# Full binary trees

```agda
module trees.full-binary-trees where
```

<details><summary>Imports</summary>

```agda
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.coproduct-types
```

</details>

## Idea

A
{{#concept "full binary tree" Agda=full-binary-tree WD="full binary tree" WDID=Q29791667}}
is a finite [directed tree](trees.directed-trees.md) in which every non-leaf
node has a specified left branch and a specified right branch. More precisely, a
full binary tree consists of a root, a left full binary subtree and a right full
binary subtree.

## Definitions

### Full binary trees

```agda
data full-binary-tree : UU lzero where
  leaf-full-binary-tree : full-binary-tree
  join-full-binary-tree : (s t : full-binary-tree) → full-binary-tree
```

### The nodes of a full binary tree

```agda
node-full-binary-tree : full-binary-tree → UU lzero
node-full-binary-tree leaf-full-binary-tree = unit
node-full-binary-tree (join-full-binary-tree G H) =
  node-full-binary-tree G + node-full-binary-tree H
```
