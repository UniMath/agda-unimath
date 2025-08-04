# Labeled full binary trees

```agda
module trees.labeled-full-binary-trees where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.universe-levels

open import trees.full-binary-trees
```

</details>

## Idea

For a type `X`, an
{{#concept "`X`-labeling" Disambiguation="of full binary trees" Agda=labeling-full-binary-tree}}
of a [full binary tree](trees.full-binary-trees.md) `T` is a map from the nodes
of `T` to `X`. A
{{#concept "labeled full binary tree" Agda=labeled-full-binary-tree}} is a pair
of a full binary tree and a labeling.

## Definition

```agda
module _
  {l : Level} (X : UU l)
  where

  labeling-full-binary-tree : (T : full-binary-tree) → UU l
  labeling-full-binary-tree T = node-full-binary-tree T → X

  labeled-full-binary-tree : UU l
  labeled-full-binary-tree =
    Σ full-binary-tree (λ T → labeling-full-binary-tree T)
```

### The weight of a labeled full binary tree

This is simply the weight of its underlying full binary tree.

```agda
  weight-labeled-full-binary-tree : labeled-full-binary-tree → ℕ
  weight-labeled-full-binary-tree (T , _) = weight-full-binary-tree T
```
