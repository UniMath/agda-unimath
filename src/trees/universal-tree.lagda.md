# The universal tree

```agda
{-# OPTIONS --guardedness #-}

module trees.universal-tree where
```

<details><summary>Imports</summary>

```agda
open import foundation.unit-type
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

### The universal large tree

The universal large tree carries extra level parameters with it. This is to
ensure that it contains a tree of
[iterated type families](foundation.iterated-type-families.md) of which each
type family `A_i` is assigned its own universe level.

```agda
record Universal-Large-Tree : UUω
  where
  coinductive
  field
    level-Universal-Large-Tree : Level
    type-Universal-Large-Tree : UU level-Universal-Large-Tree
    branch-Universal-large-Tree :
      (x : type-Universal-Large-Tree) → Universal-Large-Tree

open Universal-Large-Tree public

point-Universal-Large-Tree : Universal-Large-Tree
level-Universal-Large-Tree point-Universal-Large-Tree =
  lzero
type-Universal-Large-Tree point-Universal-Large-Tree =
  unit
branch-Universal-large-Tree point-Universal-Large-Tree x =
  point-Universal-Large-Tree
```
