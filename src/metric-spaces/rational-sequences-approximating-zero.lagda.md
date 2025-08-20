# Rational sequences approximating zero

```agda
{-# OPTIONS --lossy-unification #-}

module metric-spaces.rational-sequences-approximating-zero where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.absolute-value-rational-numbers
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.difference-rational-numbers
open import elementary-number-theory.distance-rational-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonnegative-rational-numbers
open import elementary-number-theory.nonzero-natural-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-natural-numbers
open import elementary-number-theory.strict-inequality-rational-numbers
open import elementary-number-theory.unit-fractions-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.inhabited-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sequences
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.cauchy-approximations-metric-spaces
open import metric-spaces.convergent-cauchy-approximations-metric-spaces
open import metric-spaces.limits-of-cauchy-approximations-metric-spaces
open import metric-spaces.limits-of-sequences-metric-spaces
open import metric-spaces.metric-space-of-rational-numbers
open import metric-spaces.metric-spaces
open import metric-spaces.rational-approximations-of-zero
open import metric-spaces.rational-cauchy-approximations
open import metric-spaces.sequences-metric-spaces
```

</details>

## Idea

A [sequence](foundation.sequences.md) of
[rational numbers](elementary-number-theory.rational-numbers.md) is an
{{#concept "approximation of zero" Disambiguation="sequence of rational numbers" Agda=zero-limit-sequence-ℚ}}
if it [converges](metric-spaces.limits-of-sequences-metric-spaces.md) to 0 in
the
[standard metric space of rational numbers](metric-spaces.metric-space-of-rational-numbers.md).

## Definitions

```agda
is-zero-limit-prop-sequence-ℚ : sequence ℚ → Prop lzero
is-zero-limit-prop-sequence-ℚ u =
  is-limit-prop-sequence-Metric-Space
    metric-space-ℚ
    u
    zero-ℚ

is-zero-limit-sequence-ℚ : sequence ℚ → UU lzero
is-zero-limit-sequence-ℚ u =
  type-Prop (is-zero-limit-prop-sequence-ℚ u)

zero-limit-sequence-ℚ : UU lzero
zero-limit-sequence-ℚ =
  type-subtype is-zero-limit-prop-sequence-ℚ

module _
  (u : zero-limit-sequence-ℚ)
  where

  seq-zero-limit-sequence-ℚ : sequence ℚ
  seq-zero-limit-sequence-ℚ = pr1 u

  is-zero-limit-seq-zero-limit-sequence-ℚ :
    is-limit-sequence-Metric-Space
      ( metric-space-ℚ)
      ( seq-zero-limit-sequence-ℚ)
      ( zero-ℚ)
  is-zero-limit-seq-zero-limit-sequence-ℚ = pr2 u
```

## Properties

### The sequence `n ↦ 1/(n+1)` is an approximation of zero

```agda
abstract
  is-zero-limit-reciprocal-rational-succ-ℕ :
    is-zero-limit-sequence-ℚ reciprocal-rational-succ-ℕ
  is-zero-limit-reciprocal-rational-succ-ℕ =
    unit-trunc-Prop
      ( modulus-reciprocal-rational-succ-ℕ ,
        is-zero-limit-modulus-reciprocal-rational-succ-ℕ)
    where

    modulus-reciprocal-rational-succ-ℕ : ℚ⁺ → ℕ
    modulus-reciprocal-rational-succ-ℕ =
      nat-ℕ⁺ ∘ pr1 ∘ smaller-reciprocal-ℚ⁺

    le-leq-modulus-reciprocal-succ-ℕ :
      (ε : ℚ⁺) (n : ℕ) →
      leq-ℕ
        ( modulus-reciprocal-rational-succ-ℕ ε)
        ( n) →
      le-ℚ
        ( reciprocal-rational-succ-ℕ n)
        ( rational-ℚ⁺ ε)
    le-leq-modulus-reciprocal-succ-ℕ ε n H =
      concatenate-leq-le-ℚ
        ( reciprocal-rational-succ-ℕ n)
        ( reciprocal-rational-ℕ⁺
          ( pr1 (smaller-reciprocal-ℚ⁺ ε)))
        ( rational-ℚ⁺ ε)
        ( leq-reciprocal-rational-ℕ⁺
          ( pr1 (smaller-reciprocal-ℚ⁺ ε))
          ( succ-nonzero-ℕ' n)
          ( leq-le-ℕ
            ( modulus-reciprocal-rational-succ-ℕ ε)
            ( nat-ℕ⁺ (succ-nonzero-ℕ' n))
            ( le-succ-leq-ℕ
              ( modulus-reciprocal-rational-succ-ℕ ε)
              ( n)
              ( H))))
        ( pr2 (smaller-reciprocal-ℚ⁺ ε))

    is-zero-limit-modulus-reciprocal-rational-succ-ℕ :
      is-limit-modulus-sequence-Metric-Space
        ( metric-space-ℚ)
        ( reciprocal-rational-succ-ℕ)
        ( zero-ℚ)
        ( modulus-reciprocal-rational-succ-ℕ)
    is-zero-limit-modulus-reciprocal-rational-succ-ℕ ε n H =
      neighborhood-leq-dist-ℚ
        ( ε)
        ( reciprocal-rational-succ-ℕ n)
        ( zero-ℚ)
        ( leq-le-ℚ
          { rational-dist-ℚ (reciprocal-rational-succ-ℕ n) zero-ℚ}
          { rational-ℚ⁺ ε}
          ( inv-tr
            ( λ q → le-ℚ q (rational-ℚ⁺ ε))
            ( ap
              ( rational-ℚ⁰⁺)
              ( right-zero-law-dist-ℚ
                ( reciprocal-rational-succ-ℕ n) ∙
                ( abs-rational-ℚ⁰⁺
                  ( nonnegative-ℚ⁺
                    ( positive-reciprocal-rational-succ-ℕ n)))))
            ( le-leq-modulus-reciprocal-succ-ℕ ε n H)))

zero-limit-reciprocal-succ-ℕ : zero-limit-sequence-ℚ
zero-limit-reciprocal-succ-ℕ =
  ( reciprocal-rational-succ-ℕ , is-zero-limit-reciprocal-rational-succ-ℕ)
```

### A sequence with absolute value lesser then an approximation of zero is an approximation of zero

```agda
module _
  ( u : sequence ℚ) (v : zero-limit-sequence-ℚ)
  ( |u|≤v :
    (n : ℕ) →
    leq-ℚ (rational-abs-ℚ (u n)) (seq-zero-limit-sequence-ℚ v n))
  where

  abstract
    tr-is-modulus-leq-abs-zero-limit-sequence-ℚ :
      (m : ℚ⁺ → ℕ) →
      is-limit-modulus-sequence-Metric-Space
        ( metric-space-ℚ)
        ( seq-zero-limit-sequence-ℚ v)
        ( zero-ℚ)
        ( m) →
      is-limit-modulus-sequence-Metric-Space
        ( metric-space-ℚ)
        ( u)
        ( zero-ℚ)
        ( m)
    tr-is-modulus-leq-abs-zero-limit-sequence-ℚ m H ε n K =
      neighborhood-leq-dist-ℚ
        ( ε)
        ( u n)
        ( zero-ℚ)
        ( transitive-leq-ℚ
          ( rational-dist-ℚ (u n) zero-ℚ)
          ( seq-zero-limit-sequence-ℚ v n)
          ( rational-ℚ⁺ ε)
          ( tr
            ( leq-ℚ (seq-zero-limit-sequence-ℚ v n))
            ( left-unit-law-add-ℚ (rational-ℚ⁺ ε))
            ( pr2 (H ε n K)))
          ( inv-tr
            ( λ q → leq-ℚ q (seq-zero-limit-sequence-ℚ v n))
            ( ap rational-ℚ⁰⁺ (right-zero-law-dist-ℚ (u n)))
            ( |u|≤v n)))

    is-zero-limit-leq-abs-zero-limit-sequence-ℚ :
      is-zero-limit-sequence-ℚ u
    is-zero-limit-leq-abs-zero-limit-sequence-ℚ =
      map-is-inhabited
        ( tot tr-is-modulus-leq-abs-zero-limit-sequence-ℚ)
        ( is-zero-limit-seq-zero-limit-sequence-ℚ v)
```

### Any rational approximation of zero defines a sequence approximating zero

```agda
module _
  (f : approximation-of-zero-ℚ)
  where

  seq-approximation-of-zero-ℚ : sequence ℚ
  seq-approximation-of-zero-ℚ n =
    map-approximation-of-zero-ℚ
      ( f)
      ( positive-reciprocal-rational-ℕ⁺ (succ-nonzero-ℕ' n))

  is-zero-limit-seq-approximation-of-zero-ℚ :
    is-zero-limit-sequence-ℚ seq-approximation-of-zero-ℚ
  is-zero-limit-seq-approximation-of-zero-ℚ =
    is-zero-limit-leq-abs-zero-limit-sequence-ℚ
      ( seq-approximation-of-zero-ℚ)
      ( zero-limit-reciprocal-succ-ℕ)
      ( is-approximation-of-zero-map-approximation-of-zero-ℚ f ∘
        positive-reciprocal-rational-succ-ℕ)

  zero-limit-seq-approximation-of-zero-ℚ : zero-limit-sequence-ℚ
  zero-limit-seq-approximation-of-zero-ℚ =
    seq-approximation-of-zero-ℚ ,
    is-zero-limit-seq-approximation-of-zero-ℚ
```
