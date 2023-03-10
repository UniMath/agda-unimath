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

Given a G-set `X`, the stabilizer group at an element `x` of `X` is the subgroup of elements `g` of `G` that keep `x` fixed.

## Definition

```agda
module _
  {l1 l2 : Level} (G : Group l1) (X : Abstract-Group-Action G l2)
  where

  type-stabilizer-Abstract-Group-Action :
    type-Abstract-Group-Action G X → UU (l1 ⊔ l2)
  type-stabilizer-Abstract-Group-Action x =
    Σ (type-Group G) (λ g → Id (mul-Abstract-Group-Action G X g x) x)
```
