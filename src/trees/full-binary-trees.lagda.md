# Full binary trees

```agda
open import foundation.function-extensionality-axiom

module
  trees.full-binary-trees
  (funext : function-extensionality)
  where
```

<details><sumary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.empty-types funext
open import foundation.universe-levels

open import univalent-combinatorics.standard-finite-types funext
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
