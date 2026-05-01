# Increasing finite sequences in posets

```agda
module order-theory.increasing-finite-sequences-posets where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-standard-finite-types
open import elementary-number-theory.natural-numbers

open import foundation.conjunction
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.subtypes
open import foundation.unit-type
open import foundation.universe-levels

open import lists.finite-sequences

open import order-theory.opposite-posets
open import order-theory.order-preserving-maps-posets
open import order-theory.posets

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

A [finite sequence](lists.finite-sequences.md) of elements of a
[poset](order-theory.posets.md) is
{{#concept "increasing" Disambiguation="finite sequence in a poset" Agda=is-increasing-fin-sequence-type-Poset}}
if each element is less than or equal to the next.

## Definition

```agda
module _
  {l1 l2 : Level}
  (P : Poset l1 l2)
  where

  is-increasing-prop-fin-sequence-type-Poset :
    (n : ℕ) → subtype l2 (fin-sequence (type-Poset P) n)
  is-increasing-prop-fin-sequence-type-Poset n =
    preserves-order-prop-Poset (Fin-Poset n) P

  is-increasing-fin-sequence-type-Poset :
    (n : ℕ) → fin-sequence (type-Poset P) n → UU l2
  is-increasing-fin-sequence-type-Poset n =
    is-in-subtype (is-increasing-prop-fin-sequence-type-Poset n)

  increasing-fin-sequence-type-Poset : ℕ → UU (l1 ⊔ l2)
  increasing-fin-sequence-type-Poset n =
    type-subtype (is-increasing-prop-fin-sequence-type-Poset n)

module _
  {l1 l2 : Level}
  (P : Poset l1 l2)
  (n : ℕ)
  ((u , H) : increasing-fin-sequence-type-Poset P n)
  where

  fin-sequence-increasing-fin-sequence-type-Poset :
    fin-sequence (type-Poset P) n
  fin-sequence-increasing-fin-sequence-type-Poset = u

  is-increasing-fin-sequence-increasing-fin-sequence-type-Poset :
    is-increasing-fin-sequence-type-Poset
      ( P)
      ( n)
      ( fin-sequence-increasing-fin-sequence-type-Poset)
  is-increasing-fin-sequence-increasing-fin-sequence-type-Poset = H
```

## Properties

### A finite sequence `a₁, ..., aₙ` is increasing if and only if `a₁ ≤ a₂ ∧ a₂ ≤ a₃ ∧ ... ∧ aₙ₋₁ ≤ aₙ`

```agda
module _
  {l1 l2 : Level}
  (P : Poset l1 l2)
  where

  is-increasing-leq-next-prop-fin-sequence-type-Poset :
    (n : ℕ) → subtype l2 (fin-sequence (type-Poset P) n)
  is-increasing-leq-next-prop-fin-sequence-type-Poset 0 _ = raise-unit-Prop l2
  is-increasing-leq-next-prop-fin-sequence-type-Poset 1 _ = raise-unit-Prop l2
  is-increasing-leq-next-prop-fin-sequence-type-Poset (succ-ℕ n@(succ-ℕ _)) u =
    ( is-increasing-leq-next-prop-fin-sequence-type-Poset
      ( n)
      ( tail-fin-sequence n u)) ∧
    ( leq-prop-Poset P (u (inl (inr star))) (u (inr star)))

  is-increasing-leq-next-fin-sequence-type-Poset :
    (n : ℕ) → fin-sequence (type-Poset P) n → UU l2
  is-increasing-leq-next-fin-sequence-type-Poset n =
    is-in-subtype (is-increasing-leq-next-prop-fin-sequence-type-Poset n)

  abstract
    is-increasing-is-increasing-leq-next-fin-sequence-type-Poset :
      (n : ℕ) (u : fin-sequence (type-Poset P) n) →
      is-increasing-leq-next-fin-sequence-type-Poset n u →
      is-increasing-fin-sequence-type-Poset P n u
    is-increasing-is-increasing-leq-next-fin-sequence-type-Poset
      (succ-ℕ _) u H (inr star) (inr star) _ =
      refl-leq-Poset P (u (inr star))
    is-increasing-is-increasing-leq-next-fin-sequence-type-Poset
      (succ-ℕ n@(succ-ℕ _)) u (incr-tail-u , u₋₂≤u₋₁) (inl i) (inr star) _ =
      transitive-leq-Poset
        ( P)
        ( u (inl i))
        ( u (inl (inr star)))
        ( u (inr star))
        ( u₋₂≤u₋₁)
        ( is-increasing-is-increasing-leq-next-fin-sequence-type-Poset
          ( n)
          ( tail-fin-sequence n u)
          ( incr-tail-u)
          ( i)
          ( inr star)
          ( star))
    is-increasing-is-increasing-leq-next-fin-sequence-type-Poset
      ( succ-ℕ n@(succ-ℕ _)) u (incr-tail-u , _) (inl i) (inl j) i≤j =
      is-increasing-is-increasing-leq-next-fin-sequence-type-Poset
        ( n)
        ( tail-fin-sequence n u)
        ( incr-tail-u)
        ( i)
        ( j)
        ( i≤j)

    is-increasing-leq-next-is-increasing-fin-sequence-type-Poset :
      (n : ℕ) (u : fin-sequence (type-Poset P) n) →
      is-increasing-fin-sequence-type-Poset P n u →
      is-increasing-leq-next-fin-sequence-type-Poset n u
    is-increasing-leq-next-is-increasing-fin-sequence-type-Poset 0 u H =
      raise-star
    is-increasing-leq-next-is-increasing-fin-sequence-type-Poset 1 u H =
      raise-star
    is-increasing-leq-next-is-increasing-fin-sequence-type-Poset
      (succ-ℕ n@(succ-ℕ _)) u H =
      ( is-increasing-leq-next-is-increasing-fin-sequence-type-Poset
          ( n)
          ( tail-fin-sequence n u)
          ( λ i j → H (inl i) (inl j)) ,
        H (inl (inr star)) (inr star) star)
```
