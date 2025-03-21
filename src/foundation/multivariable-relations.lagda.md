# Multivariable relations

```agda
module foundation.multivariable-relations where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.multivariable-correspondences
open import foundation.universe-levels

open import foundation-core.subtypes

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

A `n`-ary relation on a type `A` is a subtype of `Fin n → A`.

## Definition

```agda
multivariable-relation :
  {l1 : Level} (l2 : Level) (n : ℕ) (A : Fin n → UU l1) → UU (l1 ⊔ lsuc l2)
multivariable-relation l2 n A = subtype l2 ((i : Fin n) → A i)

module _
  {l1 l2 : Level} {n : ℕ} {A : Fin n → UU l1}
  (R : multivariable-relation l2 n A)
  where

  multivariable-correspondence-multivariable-relation :
    multivariable-correspondence l2 n A
  multivariable-correspondence-multivariable-relation =
    is-in-subtype R
```
