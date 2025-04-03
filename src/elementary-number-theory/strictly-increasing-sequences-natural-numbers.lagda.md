# Strictly increasing sequences of natural numbers

```agda
module elementary-number-theory.strictly-increasing-sequences-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers
open import elementary-number-theory.well-ordering-principle-natural-numbers

open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.negation
open import foundation.propositions
open import foundation.sequences
open import foundation.subtypes
open import foundation.universe-levels

open import order-theory.strict-order-preserving-maps
open import order-theory.strictly-increasing-sequences-strictly-preordered-sets
```

</details>

## Idea

A [sequence](foundation.sequences.md) of
[natural numbers](elementary-number-theory.natural-numbers.md) is
{{#concept "strictly increasing" Disambiguation="sequence of natural numbers" Agda=is-strictly-increasing-sequence-ℕ}}
if it preserves
[strict inequality](elementary-number-theory.strict-inequality-natural-numbers.md)
on the natural numbers.

Strictly increasing sequences of natural numbers are unbounded.

## Definitions

### Strictly increasing sequences of natural numbers

```agda
strictly-increasing-sequence-ℕ : UU lzero
strictly-increasing-sequence-ℕ =
  hom-Strictly-Preordered-Set ℕ-Strict-Preordered-Set ℕ-Strict-Preordered-Set

is-strictly-increasing-prop-sequence-ℕ : subtype lzero (sequence ℕ)
is-strictly-increasing-prop-sequence-ℕ =
  is-strictly-increasing-prop-sequence-Strictly-Preordered-Set
    ℕ-Strict-Preordered-Set

is-strictly-increasing-sequence-ℕ : sequence ℕ → UU lzero
is-strictly-increasing-sequence-ℕ =
  is-strictly-increasing-sequence-Strictly-Preordered-Set
    ℕ-Strict-Preordered-Set

is-prop-is-strictly-increasing-sequence-ℕ :
  (f : sequence ℕ) → is-prop (is-strictly-increasing-sequence-ℕ f)
is-prop-is-strictly-increasing-sequence-ℕ =
  is-prop-is-strictly-increasing-sequence-Strictly-Preordered-Set
    ℕ-Strict-Preordered-Set
```

```agda
module _
  (f : strictly-increasing-sequence-ℕ)
  where

  seq-strictly-increasing-sequence-ℕ : sequence ℕ
  seq-strictly-increasing-sequence-ℕ = pr1 f

  is-strictly-increasing-seq-strictly-increasing-sequence-ℕ :
    is-strictly-increasing-sequence-Strictly-Preordered-Set
      ℕ-Strict-Preordered-Set
      seq-strictly-increasing-sequence-ℕ
  is-strictly-increasing-seq-strictly-increasing-sequence-ℕ = pr2 f
```

## Properties

### The identity is strictly increasing

```agda
strictly-increasing-id-ℕ : strictly-increasing-sequence-ℕ
strictly-increasing-id-ℕ = id , λ i j H → H
```

### Composition of strictly increasing sequences of natural numbers

```agda
module _
  (v u : strictly-increasing-sequence-ℕ)
  where

  comp-strictly-increasing-sequence-ℕ : strictly-increasing-sequence-ℕ
  comp-strictly-increasing-sequence-ℕ =
    comp-hom-Strictly-Preordered-Set
      ℕ-Strict-Preordered-Set
      ℕ-Strict-Preordered-Set
      ℕ-Strict-Preordered-Set
      v
      u

  compute-comp-strictly-increasing-sequence-ℕ :
    ( seq-strictly-increasing-sequence-ℕ v ∘
      seq-strictly-increasing-sequence-ℕ u) ＝
    ( seq-strictly-increasing-sequence-ℕ comp-strictly-increasing-sequence-ℕ)
  compute-comp-strictly-increasing-sequence-ℕ = refl
```

### Strictly increasing sequences of natural numbers are unbounded

```agda
module _
  ( f : ℕ → ℕ)
  ( H :
    is-strictly-increasing-sequence-Strictly-Preordered-Set
      ℕ-Strict-Preordered-Set
      f)
  where

  is-unbounded-is-strictly-increasing-sequence-ℕ :
    (M : ℕ) → Σ ℕ (λ N → (p : ℕ) → leq-ℕ N p → leq-ℕ M (f p))
  is-unbounded-is-strictly-increasing-sequence-ℕ zero-ℕ =
    ( zero-ℕ , λ p K → leq-zero-ℕ (f p))
  is-unbounded-is-strictly-increasing-sequence-ℕ (succ-ℕ M) =
    map-Σ
      ( λ N → (p : ℕ) → leq-ℕ N p → leq-ℕ (succ-ℕ M) (f p))
      ( succ-ℕ)
      ( λ N K p I →
        leq-succ-le-ℕ M (f p)
          ( concatenate-leq-le-ℕ
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
      ( is-unbounded-is-strictly-increasing-sequence-ℕ M)

  modulus-is-unbounded-is-strictly-increasing-sequence-ℕ : ℕ → ℕ
  modulus-is-unbounded-is-strictly-increasing-sequence-ℕ M =
    pr1 (is-unbounded-is-strictly-increasing-sequence-ℕ M)

  leq-bound-is-strictly-increasing-sequence-ℕ :
    (M p : ℕ) →
    leq-ℕ (modulus-is-unbounded-is-strictly-increasing-sequence-ℕ M) p →
    leq-ℕ M (f p)
  leq-bound-is-strictly-increasing-sequence-ℕ M =
    pr2 (is-unbounded-is-strictly-increasing-sequence-ℕ M)
```

```agda
module _
  (f : strictly-increasing-sequence-ℕ)
  where

  is-unbounded-strictly-increasing-sequence-ℕ :
    (M : ℕ) →
    Σ ℕ
      ( λ N →
        (p : ℕ) →
        leq-ℕ N p →
        leq-ℕ M (seq-strictly-increasing-sequence-ℕ f p))
  is-unbounded-strictly-increasing-sequence-ℕ =
    is-unbounded-is-strictly-increasing-sequence-ℕ
      ( seq-strictly-increasing-sequence-ℕ f)
      ( is-strictly-increasing-seq-strictly-increasing-sequence-ℕ f)
```
