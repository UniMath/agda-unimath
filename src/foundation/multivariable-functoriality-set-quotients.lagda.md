# Multivariable functoriality of set quotients

```agda
module foundation.multivariable-functoriality-set-quotients where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.functoriality-set-quotients
open import foundation.set-quotients
open import foundation.universe-levels
open import foundation.vectors-set-quotients

open import foundation-core.equivalence-relations
open import foundation-core.function-types
open import foundation-core.homotopies

open import linear-algebra.vectors

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Say we have a family of types `A1`, ..., `An` each equipped with an equivalence
relation `Ri`, as well as a type `X` equipped with an equivalence relation `S`,
Then, any multivariable operation from the `Ai`s to the `X` that respects the
equivalence relations extends uniquely to a multivariable operation from the
`Ai/Ri`s to `X/S`.

## Definition

### `n`-ary hom of equivalence relation

```agda
module _
  { l1 l2 l3 l4 : Level}
  ( n : ℕ)
  ( A : functional-vec (UU l1) n)
  ( R : (i : Fin n) → equivalence-relation l2 (A i))
  { X : UU l3} (S : equivalence-relation l4 X)
  where

  multivariable-map-set-quotient :
    ( h : hom-equivalence-relation (all-sim-equivalence-relation n A R) S) →
    set-quotient-vector n A R → set-quotient S
  multivariable-map-set-quotient =
    map-is-set-quotient
      ( all-sim-equivalence-relation n A R)
      ( set-quotient-vector-Set n A R)
      ( reflecting-map-quotient-vector-map n A R)
      ( S)
      ( quotient-Set S)
      ( reflecting-map-quotient-map S)
      ( is-set-quotient-vector-set-quotient n A R)
      ( is-set-quotient-set-quotient S)

  compute-multivariable-map-set-quotient :
    ( h : hom-equivalence-relation (all-sim-equivalence-relation n A R) S) →
    ( multivariable-map-set-quotient h ∘
      quotient-vector-map n A R) ~
    ( quotient-map S ∘
      map-hom-equivalence-relation (all-sim-equivalence-relation n A R) S h)
  compute-multivariable-map-set-quotient =
    coherence-square-map-is-set-quotient
      ( all-sim-equivalence-relation n A R)
      ( set-quotient-vector-Set n A R)
      ( reflecting-map-quotient-vector-map n A R)
      ( S)
      ( quotient-Set S)
      ( reflecting-map-quotient-map S)
      ( is-set-quotient-vector-set-quotient n A R)
      ( is-set-quotient-set-quotient S)
```
