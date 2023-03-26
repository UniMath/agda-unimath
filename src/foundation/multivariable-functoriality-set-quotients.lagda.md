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
open import foundation-core.equivalences

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

### n-ary hom of equivalence relation

```agda
module _
  { l1 l2 l3 l4 : Level}
  ( n : ℕ)
  ( As : functional-vec (UU l1) n)
  ( Rs : (i : Fin n) → Eq-Rel l2 (As i))
  { X : UU l3} (S : Eq-Rel l4 X)
  where

  multivariable-map-set-quotient :
    (h : hom-Eq-Rel (all-sim-Eq-Rel n As Rs) S) →
    set-quotient-vector n As Rs → set-quotient S
  multivariable-map-set-quotient h as =
    map-set-quotient (all-sim-Eq-Rel n As Rs) S h
      ( map-equiv (equiv-set-quotient-vector n As Rs) as)
```
