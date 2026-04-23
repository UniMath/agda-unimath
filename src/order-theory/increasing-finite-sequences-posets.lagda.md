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
open import foundation.homotopies
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.subtypes
open import foundation.unit-type
open import foundation.universe-levels

open import lists.finite-sequences
open import lists.pairs-of-successive-elements-finite-sequences

open import order-theory.closed-intervals-posets
open import order-theory.opposite-posets
open import order-theory.order-preserving-maps-posets
open import order-theory.posets

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

A [finite sequence](lists.finite-sequences.md) of elements of a
[poset](order-theory.posets.md) is
{{#concept "increasing" Disambiguation="finite sequence in a poset" Agda=is-increasing-fin-sequence-Poset}}
if each element is less than or equal to the next.

## Definition

```agda
module _
  {l1 l2 : Level}
  (P : Poset l1 l2)
  where

  is-increasing-prop-fin-sequence-type-Poset :
    (n : ℕ) → subtype l2 (fin-sequence (type-Poset P) n)
  is-increasing-prop-fin-sequence-type-Poset 0 _ = raise-unit-Prop l2
  is-increasing-prop-fin-sequence-type-Poset 1 _ = raise-unit-Prop l2
  is-increasing-prop-fin-sequence-type-Poset (succ-ℕ (succ-ℕ n)) u =
    ( leq-prop-Poset
      ( P)
      ( u (neg-one-Fin (succ-ℕ n)))
      ( u (neg-two-Fin (succ-ℕ n)))) ∧
    ( is-increasing-prop-fin-sequence-type-Poset
      ( succ-ℕ n)
      ( tail-fin-sequence (succ-ℕ n) u))

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

### A finite sequence in a poset `P` is increasing if and only if it is an order-reversing map from `Fin n` to `P`

The
[standard ordering](elementary-number-theory.inequality-standard-finite-types.md)
on the [standard finite types](univalent-combinatorics.standard-finite-types.md)
defines `neg-one-Fin n` as the greatest element of `Fin (succ-ℕ n)`, but finite
sequences use `neg-one-Fin n` as the head, which is conventionally the first
element of the sequence.

We choose to adopt the convention that the head of an increasing sequence is its
least element, requiring us to reverse the order of `Fin n`.

```agda
module _
  {l1 l2 : Level}
  (P : Poset l1 l2)
  where

  abstract
    reverses-order-is-increasing-fin-sequence-type-Poset :
      (n : ℕ) (u : fin-sequence (type-Poset P) n) →
      is-increasing-fin-sequence-type-Poset P n u →
      preserves-order-Poset (opposite-Poset (Fin-Poset n)) P u
    reverses-order-is-increasing-fin-sequence-type-Poset
      (succ-ℕ n) u _ (inr star) (inr star) _ =
      refl-leq-Poset P (u (inr star))
    reverses-order-is-increasing-fin-sequence-type-Poset
      (succ-ℕ (succ-ℕ n)) u (u₁≤u₂ , increasing-tail-u) (inr star) (inl j) _ =
      transitive-leq-Poset
        ( P)
        ( u (inr star))
        ( u (inl (inr star)))
        ( u (inl j))
        ( reverses-order-is-increasing-fin-sequence-type-Poset
          ( succ-ℕ n)
          ( tail-fin-sequence (succ-ℕ n) u)
          ( increasing-tail-u)
          ( inr star)
          ( j)
          ( star))
        ( u₁≤u₂)
    reverses-order-is-increasing-fin-sequence-type-Poset
      (succ-ℕ (succ-ℕ n)) u (u₁≤u₂ , increasing-tail-u) (inl i) (inl j) j≤i =
      reverses-order-is-increasing-fin-sequence-type-Poset
        ( succ-ℕ n)
        ( tail-fin-sequence (succ-ℕ n) u)
        ( increasing-tail-u)
        ( i)
        ( j)
        ( j≤i)

    is-increasing-reverses-order-fin-sequence-type-Poset :
      (n : ℕ) (u : fin-sequence (type-Poset P) n) →
      preserves-order-Poset (opposite-Poset (Fin-Poset n)) P u →
      is-increasing-fin-sequence-type-Poset P n u
    is-increasing-reverses-order-fin-sequence-type-Poset 0 u H = raise-star
    is-increasing-reverses-order-fin-sequence-type-Poset 1 u H = raise-star
    is-increasing-reverses-order-fin-sequence-type-Poset
      (succ-ℕ (succ-ℕ n)) u H =
      ( H (inr star) (neg-two-Fin (succ-ℕ n)) star ,
        is-increasing-reverses-order-fin-sequence-type-Poset
          ( succ-ℕ n)
          ( tail-fin-sequence (succ-ℕ n) u)
          ( λ i j → H (inl i) (inl j)))

  reverses-order-iff-is-increasing-fin-sequence-type-Poset :
    (n : ℕ) (u : fin-sequence (type-Poset P) n) →
    is-increasing-fin-sequence-type-Poset P n u ↔
    preserves-order-Poset (opposite-Poset (Fin-Poset n)) P u
  reverses-order-iff-is-increasing-fin-sequence-type-Poset n u =
    ( reverses-order-is-increasing-fin-sequence-type-Poset n u ,
      is-increasing-reverses-order-fin-sequence-type-Poset n u)

  reverses-order-increasing-fin-sequence-type-Poset :
    (n : ℕ) (u : increasing-fin-sequence-type-Poset P n) →
    preserves-order-Poset
      ( opposite-Poset (Fin-Poset n))
      ( P)
      ( fin-sequence-increasing-fin-sequence-type-Poset P n u)
  reverses-order-increasing-fin-sequence-type-Poset n =
    ind-Σ (reverses-order-is-increasing-fin-sequence-type-Poset n)
```

### Given an increasing sequence `a₁ ≤ a₂ ≤ ... ≤ aₙ`, the sequence of intervals `[a₁, a₂], [a₂, a₃], ..., [aₙ₋₁, aₙ]`

```agda
module _
  {l1 l2 : Level}
  (P : Poset l1 l2)
  where

  closed-intervals-increasing-fin-sequence-type-Poset :
    (n : ℕ) → increasing-fin-sequence-type-Poset P (succ-ℕ n) →
    fin-sequence (closed-interval-Poset P) n
  closed-intervals-increasing-fin-sequence-type-Poset
    ( succ-ℕ n)
    ( u , u₁≤u₂ , is-increasing-tail-u) =
    cons-fin-sequence
      ( n)
      ( ( head-fin-sequence (succ-ℕ n) u ,
          head-fin-sequence n (tail-fin-sequence (succ-ℕ n) u)) ,
        u₁≤u₂)
      ( closed-intervals-increasing-fin-sequence-type-Poset
        ( n)
        ( tail-fin-sequence (succ-ℕ n) u , is-increasing-tail-u))

  closed-intervals-increasing-fin-sequence-type-Poset' :
    (n : ℕ) → increasing-fin-sequence-type-Poset P (succ-ℕ n) →
    fin-sequence (closed-interval-Poset P) n
  closed-intervals-increasing-fin-sequence-type-Poset' n (u , H) i =
    ( pair-succ-fin-sequence' n u i ,
      reverses-order-is-increasing-fin-sequence-type-Poset P
        ( succ-ℕ n)
        ( u)
        ( H)
        ( skip-zero-Fin n i)
        ( inl-Fin n i)
        ( leq-succ-Fin n i))

  abstract
    htpy-closed-intervals-increasing-fin-sequence-type-Poset' :
      (n : ℕ) (u : increasing-fin-sequence-type-Poset P (succ-ℕ n)) →
      closed-intervals-increasing-fin-sequence-type-Poset n u ~
      closed-intervals-increasing-fin-sequence-type-Poset' n u
    htpy-closed-intervals-increasing-fin-sequence-type-Poset'
      (succ-ℕ n) (u , _ , H) (inl i) =
      htpy-closed-intervals-increasing-fin-sequence-type-Poset'
        ( n)
        ( tail-fin-sequence (succ-ℕ n) u , H)
        ( i)
    htpy-closed-intervals-increasing-fin-sequence-type-Poset'
      (succ-ℕ n) (u , _ , _) (inr star) =
      eq-type-subtype
        ( ind-Σ (leq-prop-Poset P))
        ( refl)
```
