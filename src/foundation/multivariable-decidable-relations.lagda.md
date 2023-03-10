# Multivariable decidable relations

```agda
module foundation.multivariable-decidable-relations where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.decidable-subtypes
open import foundation.multivariable-correspondences
open import foundation.multivariable-relations
open import foundation.universe-levels

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Consider a family of types `A i` indexed by `i : Fin n`. An `n`-ary decidable relation on the tuples of elements of the `A i` is a decidable subtype of the product of the `A i`.

## Definition

```agda
multivariable-decidable-relation :
  {l1 : Level} (l2 : Level) (n : ℕ) (A : Fin n → UU l1) → UU (l1 ⊔ lsuc l2)
multivariable-decidable-relation l2 n A =
  decidable-subtype l2 ((i : Fin n) → A i)

module _
  {l1 l2 : Level} {n : ℕ} {A : Fin n → UU l1}
  (R : multivariable-decidable-relation l2 n A)
  where

  multivariable-relation-multivariable-decidable-relation :
    multivariable-relation l2 n A
  multivariable-relation-multivariable-decidable-relation =
    subtype-decidable-subtype R

  multivariable-correspondence-multivariable-decidable-relation :
    multivariable-correspondence l2 n A
  multivariable-correspondence-multivariable-decidable-relation =
    is-in-decidable-subtype R
```
