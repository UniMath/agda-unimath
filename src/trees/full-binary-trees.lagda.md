# Full binary trees

```agda
module trees.full-binary-trees where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

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

### The weight of a full binary tree

This counts the number of nodes in `T : full-binary-tree` and can be thought of
as an arboreal version of the length of a [list](lists.lists.md).

```agda
weight-full-binary-tree : full-binary-tree → ℕ
weight-full-binary-tree leaf-full-binary-tree = zero-ℕ
weight-full-binary-tree (join-full-binary-tree T U) =
  weight-full-binary-tree T +ℕ weight-full-binary-tree U
```
