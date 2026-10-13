# Increasing arrays in posets

```agda
module order-theory.increasing-arrays-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.subtypes
open import foundation.universe-levels

open import lists.arrays
open import lists.nonempty-arrays

open import order-theory.increasing-finite-sequences-posets
open import order-theory.posets
```

</details>

## Idea

An [array](lists.arrays.md) in a [poset](order-theory.posets.md) is
{{#concept "increasing" Disambiguation="array in a poset" Agda=is-increasing-array-type-Poset}}
if its associated [finite sequence](lists.finite-sequences.md) is
[increasing](order-theory.increasing-finite-sequences-posets.md).

## Definition

```agda
module _
  {l1 l2 : Level}
  (P : Poset l1 l2)
  where

  is-increasing-prop-array-type-Poset : subtype l2 (array (type-Poset P))
  is-increasing-prop-array-type-Poset (n , u) =
    is-increasing-prop-fin-sequence-type-Poset P n u

  is-increasing-array-type-Poset : array (type-Poset P) → UU l2
  is-increasing-array-type-Poset =
    is-in-subtype is-increasing-prop-array-type-Poset

  increasing-array-type-Poset : UU (l1 ⊔ l2)
  increasing-array-type-Poset =
    type-subtype is-increasing-prop-array-type-Poset
```
