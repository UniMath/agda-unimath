# Stabilizer groups

```agda
module group-theory.stabilizer-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.group-actions
open import group-theory.groups
```

</details>

## Idea

Given a G-set `X`, the stabilizer group at an element `x` of `X` is the subgroup
of elements `g` of `G` that keep `x` fixed.

## Definition

```agda
module _
  {l1 l2 : Level} (G : Group l1) (X : action-Group G l2)
  where

  type-stabilizer-action-Group :
    type-action-Group G X → UU (l1 ⊔ l2)
  type-stabilizer-action-Group x =
    Σ (type-Group G) (λ g → Id (mul-action-Group G X g x) x)
```
