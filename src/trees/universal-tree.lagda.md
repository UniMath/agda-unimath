# The universal tree

```agda
{-# OPTIONS --guardedness #-}

module trees.universal-tree where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels
```

</details>

## Idea

The universal tree is the coinductive type associated to the
[polynomial endofunctor](trees.polynomial-endofunctors.md)

```text
  X ↦ Σ 𝒰 (λ T → Xᵀ).
```

Note that this is the same polynomial endofunctor that we used to define the
type of [multisets](trees.multisets.md), which is the universal _well-founded_
tree.

## Definitions

### The universal tree of small trees

```agda
module _
  (l : Level)
  where

  record Universal-Tree : UU (lsuc l)
    where
    coinductive
    field
      type-Universal-Tree :
        UU l
      branch-Universal-Tree :
        (x : type-Universal-Tree) → Universal-Tree

  open Universal-Tree public
```
