# Multivariable functoriality of set quotients

```agda
{-# OPTIONS --lossy-unification #-}
```

```agda
module foundation.multivariable-functoriality-set-quotients where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.multivariable-operations
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.equivalence-relations

open import linear-algebra.vectors

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Say we have a family of types `A1`, ..., `An` each equipped with an equivalence
relation `Ri`, as well as a type `X` equipped with an equivalence relation `X`,
Then, any multivariable operation from the `Ai`s to the `X` that respects the
equivalence relations extends uniquely to a multivariable operation from the `Ai/Ri`s
to `X/S`.

## Definition

### n-ary hom of equivalence relation

```agda
all-sim-Eq-Rel :
  {l1 l2 : Level}
  (n : ℕ)
  (As : functional-vec (UU l1) n)
  (Rs : (i : Fin n) → Eq-Rel l2 (As i)) →
  (as : (i : Fin n) → As i) →
  (a's : (i : Fin n) → As i) →
  UU l2
all-sim-Eq-Rel {l1} {l2} zero-ℕ As Rs as a's =
  raise-unit l2
all-sim-Eq-Rel {l1} {l2} (succ-ℕ n) As Rs as a's =
  sim-Eq-Rel (Rs (inr star)) (as (inr star)) (a's (inr star)) ×
   all-sim-Eq-Rel n
     ( λ i → As (inl-Fin n i))
     ( λ i → Rs (inl-Fin n i))
     ( λ i → as (inl-Fin n i))
     ( λ i → a's (inl-Fin n i))

preserves-sim-n-ary-map-Eq-Rel :
  {l1 l2 : Level}
  (n : ℕ)
  (As : functional-vec (UU l1) n)
  (Rs : (i : Fin n) → Eq-Rel l2 (As i)) →
  (X : UU l1) (S : Eq-Rel l2 X) →
  multivariable-operation n As X →
  UU (l1 ⊔ l2)
preserves-sim-n-ary-map-Eq-Rel n As Rs X S f =
  ( as : (i : Fin n) → As i) →
  ( a's : (i : Fin n) → As i) →
  ( all-sim-Eq-Rel n As Rs as a's) →
  ( sim-Eq-Rel S
    ( apply-multivariable-operation n As X f as)
    ( apply-multivariable-operation n As X f a's))
```
