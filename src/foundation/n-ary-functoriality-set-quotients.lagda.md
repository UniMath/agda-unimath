# n-ary functoriality of set quotients

```agda
{-# OPTIONS --lossy-unification #-}
```

```agda
module foundation.n-ary-functoriality-set-quotients where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.coproduct-types
open import foundation.cartesian-product-types
open import foundation.unit-type
open import foundation.universe-levels
open import foundation.n-ary-operations

open import foundation-core.equivalence-relations

open import linear-algebra.vectors

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Say we have a family of types `A1`, ..., `An` each equipped with an equivalence relation `Ri`,
as well as a type `X` equipped with an equivalence relation `X`,
Then, any n-ary operation from the `Ai`s to the `X` that respects the equivalence relations
extends uniquely to an n-ary operation from the `Ai/Ri`s to `X/S`.

## Definition

### n-ary hom of equivalence relation

```agda
all-sim-Eq-Rel :
  (n : ℕ)
  (I : Fin n → Level)
  (I' : Fin n → Level)
  (As : (i : Fin n) → UU (I i))
  (Rs : (i : Fin n) → Eq-Rel (I' i) (As i)) →
  (as : (i : Fin n) → As i) →
  (a's : (i : Fin n) → As i) →
  UU (max-level n I')
all-sim-Eq-Rel zero-ℕ I I' As Rs as a's = raise-unit lzero
all-sim-Eq-Rel (succ-ℕ n) I I' As Rs as a's =
   sim-Eq-Rel (Rs (inr star)) (as (inr star)) (a's (inr star)) ×
     all-sim-Eq-Rel n ( λ i → I (inl-Fin n i))
       ( λ i → I' (inl-Fin n i))
       ( λ i → As (inl-Fin n i))
       ( λ i → Rs (inl-Fin n i))
       ( λ i → as (inl-Fin n i))
       ( λ i → a's (inl-Fin n i))

preserves-sim-n-ary-map-Eq-Rel :
  (n : ℕ)
  (I : Fin n → Level)
  (I' : Fin n → Level)
  (As : (i : Fin n) → UU (I i))
  (Rs : (i : Fin n) → Eq-Rel (I' i) (As i)) →
  {l1 l2 : Level}
  (X : UU l1) (S : Eq-Rel l2 X) →
  n-ary-operation n I As X →
  UUω
preserves-sim-n-ary-map-Eq-Rel n I I' As Rs X S f =
  ( as : (i : Fin n) → As i) →
  ( a's : (i : Fin n) → As i) →
  ( all-sim-Eq-Rel n I I' As Rs as a's) →
  ( sim-Eq-Rel S
    ( apply-n-ary-operation n I As X f as)
    ( apply-n-ary-operation n I As X f a's))
```
