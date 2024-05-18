# Monotonic sequences of natural numbers

```agda
module elementary-number-theory.monotonic-sequences-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers

open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.negation
open import foundation.propositions
open import foundation.sequences
open import foundation.universe-levels
```

</details>

## Idea

Monotic sequences of natural numbers are functions `f : ℕ → ℕ` that preserve or
reverse (strict) inequality of natural numbers.

## Definitions

### Increasing sequences of natural numbers

```agda
module _
  (f : sequence ℕ)
  where

  is-increasing-prop-sequence-ℕ : Prop lzero
  is-increasing-prop-sequence-ℕ =
    Π-Prop ℕ
      ( λ i →
        Π-Prop ℕ
          ( λ j → hom-Prop (leq-ℕ-Prop i j) (leq-ℕ-Prop (f i) (f j))))

  is-increasing-sequence-ℕ : UU lzero
  is-increasing-sequence-ℕ =
    type-Prop is-increasing-prop-sequence-ℕ

  is-prop-is-increasing-sequence-ℕ :
    is-prop is-increasing-sequence-ℕ
  is-prop-is-increasing-sequence-ℕ =
    is-prop-type-Prop is-increasing-prop-sequence-ℕ
```

### Strictly increasing sequences of natural numbers

```agda
module _
  (f : sequence ℕ)
  where

  is-strictly-increasing-sequence-prop-ℕ : Prop lzero
  is-strictly-increasing-sequence-prop-ℕ =
    Π-Prop ℕ
      ( λ i →
        Π-Prop ℕ
          ( λ j → hom-Prop (le-ℕ-Prop i j) (le-ℕ-Prop (f i) (f j))))

  is-strictly-increasing-sequence-ℕ : UU lzero
  is-strictly-increasing-sequence-ℕ =
    type-Prop is-strictly-increasing-sequence-prop-ℕ

  is-prop-is-strictly-increasing-sequence-ℕ :
    is-prop is-strictly-increasing-sequence-ℕ
  is-prop-is-strictly-increasing-sequence-ℕ =
    is-prop-type-Prop is-strictly-increasing-sequence-prop-ℕ
```

### Decreasing sequences of natural numbers

```agda
module _
  (f : sequence ℕ)
  where

  is-decreasing-sequence-prop-ℕ : Prop lzero
  is-decreasing-sequence-prop-ℕ =
    Π-Prop ℕ
      ( λ i →
        Π-Prop ℕ
          ( λ j → hom-Prop (leq-ℕ-Prop i j) (leq-ℕ-Prop (f j) (f i))))

  is-decreasing-sequence-ℕ : UU lzero
  is-decreasing-sequence-ℕ = type-Prop is-decreasing-sequence-prop-ℕ

  is-prop-is-decreasing-sequence-ℕ : is-prop is-decreasing-sequence-ℕ
  is-prop-is-decreasing-sequence-ℕ =
    is-prop-type-Prop is-decreasing-sequence-prop-ℕ
```

### Strictly decreasing sequences of natural numbers

```agda
module _
  (f : sequence ℕ)
  where

  is-strictly-decreasing-sequence-prop-ℕ : Prop lzero
  is-strictly-decreasing-sequence-prop-ℕ =
    Π-Prop ℕ
      ( λ i →
        Π-Prop ℕ
          ( λ j → hom-Prop (le-ℕ-Prop i j) (le-ℕ-Prop (f j) (f i))))

  is-strictly-decreasing-sequence-ℕ : UU lzero
  is-strictly-decreasing-sequence-ℕ =
    type-Prop is-strictly-decreasing-sequence-prop-ℕ

  is-prop-is-strictly-decreasing-sequence-ℕ :
    is-prop is-strictly-decreasing-sequence-ℕ
  is-prop-is-strictly-decreasing-sequence-ℕ =
    is-prop-type-Prop is-strictly-decreasing-sequence-prop-ℕ
```

## Properties

### There exist no strictly decreasing sequences of natural numbers

```agda
no-strictly-decreasing-sequence-leq-ℕ :
  (f : sequence ℕ) →
  (N : ℕ) →
  is-strictly-decreasing-sequence-ℕ f →
  leq-ℕ (f zero-ℕ) N →
  empty
no-strictly-decreasing-sequence-leq-ℕ f zero-ℕ H =
  concatenate-le-leq-ℕ
    { f 1}
    { f 0}
    { 0}
    ( H 0 1 (succ-le-ℕ 0))
no-strictly-decreasing-sequence-leq-ℕ f (succ-ℕ N) H K =
  no-strictly-decreasing-sequence-leq-ℕ
    ( f ∘ succ-ℕ)
    ( N)
    ( λ i j → H (succ-ℕ i) (succ-ℕ j))
    ( leq-le-succ-ℕ
      ( f 1)
      ( N)
      ( concatenate-le-leq-ℕ
        { f 1}
        { f 0}
        { succ-ℕ N}
        ( H 0 1 (succ-le-ℕ 0))
        ( K)))

no-strictly-decreasing-sequence-ℕ :
  (f : sequence ℕ) → ¬ (is-strictly-decreasing-sequence-ℕ f)
no-strictly-decreasing-sequence-ℕ f H =
  no-strictly-decreasing-sequence-leq-ℕ f (f 0) H (refl-leq-ℕ (f 0))
```

### Strictly increasing sequences of natural numbers grow infinitely

```agda
module _
  (f : sequence ℕ) (H : is-strictly-increasing-sequence-ℕ f)
  where

  limit-∞-is-strictly-increasing-sequence-ℕ :
    (M : ℕ) → Σ ℕ (λ N → (p : ℕ) → leq-ℕ N p → leq-ℕ M (f p))
  limit-∞-is-strictly-increasing-sequence-ℕ zero-ℕ =
    ( zero-ℕ , λ p K → leq-zero-ℕ (f p))
  limit-∞-is-strictly-increasing-sequence-ℕ (succ-ℕ M) =
    map-Σ
      ( λ N → (p : ℕ) → leq-ℕ N p → leq-ℕ (succ-ℕ M) (f p))
      ( succ-ℕ)
      ( λ N K p I →
        leq-succ-le-ℕ M (f p)
          (concatenate-leq-le-ℕ
            { M}
            { f N}
            { f p}
            ( K N (refl-leq-ℕ N))
            ( H N p
              ( concatenate-le-leq-ℕ
                { N}
                { succ-ℕ N}
                { p}
                ( succ-le-ℕ N)
                ( I)))))
      ( limit-∞-is-strictly-increasing-sequence-ℕ M)

  modulus-limit-∞-is-strictly-increasing-sequence-ℕ : ℕ → ℕ
  modulus-limit-∞-is-strictly-increasing-sequence-ℕ M =
    pr1 (limit-∞-is-strictly-increasing-sequence-ℕ M)

  is-modulus-modulus-limit-∞-is-strictly-increasing-sequence-ℕ :
    (M p : ℕ) →
    leq-ℕ (modulus-limit-∞-is-strictly-increasing-sequence-ℕ M) p →
    leq-ℕ M (f p)
  is-modulus-modulus-limit-∞-is-strictly-increasing-sequence-ℕ M =
    pr2 (limit-∞-is-strictly-increasing-sequence-ℕ M)
```
