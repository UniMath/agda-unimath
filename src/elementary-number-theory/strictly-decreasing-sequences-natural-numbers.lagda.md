# Strictly decreasing sequences of natural numbers

```agda
module elementary-number-theory.strictly-decreasing-sequences-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.based-induction-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers

open import foundation.empty-types
open import foundation.function-types
open import foundation.negation
open import foundation.propositions
open import foundation.sequences
open import foundation.universe-levels
```

</details>

## Idea

A sequences of natural numbers is **strictly increasing** if it reverses
[strict inequality](elementary-number-theory.strict-inequality-natural-numbers.md)
of natural numbers.

Strictly decreasing sequences of natural numbers don't exist.

## Definitions

### Strictly decreasing sequences of natural numbers

```agda
module _
  (f : sequence ℕ)
  where

  is-strict-decreasing-sequence-prop-ℕ : Prop lzero
  is-strict-decreasing-sequence-prop-ℕ =
    Π-Prop ℕ
      ( λ i →
        Π-Prop ℕ
          ( λ j → hom-Prop (le-ℕ-Prop i j) (le-ℕ-Prop (f j) (f i))))

  is-strict-decreasing-sequence-ℕ : UU lzero
  is-strict-decreasing-sequence-ℕ =
    type-Prop is-strict-decreasing-sequence-prop-ℕ

  is-prop-is-strict-decreasing-sequence-ℕ :
    is-prop is-strict-decreasing-sequence-ℕ
  is-prop-is-strict-decreasing-sequence-ℕ =
    is-prop-type-Prop is-strict-decreasing-sequence-prop-ℕ
```

### Strict decreasing values of sequences of natural numbers

```agda
module _
  (f : sequence ℕ) (n : ℕ)
  where

  is-strict-decreasing-value-prop-sequence-ℕ : Prop lzero
  is-strict-decreasing-value-prop-sequence-ℕ = le-ℕ-Prop (f (succ-ℕ n)) (f n)

  is-strict-decreasing-value-sequence-ℕ : UU lzero
  is-strict-decreasing-value-sequence-ℕ =
    type-Prop is-strict-decreasing-value-prop-sequence-ℕ

  is-prop-is-strict-decreasing-value-sequence-ℕ :
    is-prop is-strict-decreasing-value-sequence-ℕ
  is-prop-is-strict-decreasing-value-sequence-ℕ =
    is-prop-type-Prop is-strict-decreasing-value-prop-sequence-ℕ
```

## Properties

### A sequence is strictly decreasing if and only if all its values are strictly strictly decreasing

```agda
module _
  (f : sequence ℕ)
  where

  strict-decreasing-value-is-strict-decreasing-sequence-ℕ :
    is-strict-decreasing-sequence-ℕ f →
    ((n : ℕ) → is-strict-decreasing-value-sequence-ℕ f n)
  strict-decreasing-value-is-strict-decreasing-sequence-ℕ H n =
    H n (succ-ℕ n) (succ-le-ℕ n)

  strict-decreasing-is-strict-decreasing-value-sequence-ℕ :
    ((n : ℕ) → is-strict-decreasing-value-sequence-ℕ f n) →
    is-strict-decreasing-sequence-ℕ f
  strict-decreasing-is-strict-decreasing-value-sequence-ℕ H p q I =
    based-ind-ℕ
      ( succ-ℕ p)
      ( λ k → le-ℕ (f k) (f p))
      ( H p)
      ( λ n J → transitive-le-ℕ (f (succ-ℕ n)) (f n) (f p) (H n))
      ( q)
      ( leq-succ-le-ℕ p q I)
```

### There exist no strictly decreasing sequences of natural numbers

```agda
no-bounded-strict-decreasing-sequence-ℕ :
  (f : sequence ℕ) →
  (N : ℕ) →
  leq-ℕ (f zero-ℕ) N →
  is-strict-decreasing-sequence-ℕ f →
  empty
no-bounded-strict-decreasing-sequence-ℕ f zero-ℕ K H =
  concatenate-le-leq-ℕ
    { f 1}
    { f 0}
    { 0}
    ( H 0 1 (succ-le-ℕ 0))
    ( K)
no-bounded-strict-decreasing-sequence-ℕ f (succ-ℕ N) K H =
  no-bounded-strict-decreasing-sequence-ℕ
    ( f ∘ succ-ℕ)
    ( N)
    ( leq-le-succ-ℕ
      ( f 1)
      ( N)
      ( concatenate-le-leq-ℕ
        { f 1}
        { f 0}
        { succ-ℕ N}
        ( H 0 1 (succ-le-ℕ 0))
        ( K)))
    ( λ i j → H (succ-ℕ i) (succ-ℕ j))

module _
  (f : sequence ℕ)
  where

  no-strict-decreasing-sequence-ℕ : ¬ (is-strict-decreasing-sequence-ℕ f)
  no-strict-decreasing-sequence-ℕ =
    no-bounded-strict-decreasing-sequence-ℕ f (f 0) (refl-leq-ℕ (f 0))

  no-strict-decreasing-value-sequence-ℕ :
    ¬ ((n : ℕ) → is-strict-decreasing-value-sequence-ℕ f n)
  no-strict-decreasing-value-sequence-ℕ =
    ( no-strict-decreasing-sequence-ℕ) ∘
    ( strict-decreasing-is-strict-decreasing-value-sequence-ℕ f)
```
