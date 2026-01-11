# The unit closed interval in the rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.unit-closed-interval-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.closed-intervals-rational-numbers
open import elementary-number-theory.floor-nonnegative-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.multiplication-nonnegative-rational-numbers
open import elementary-number-theory.multiplication-positive-rational-numbers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.multiplicative-group-of-positive-rational-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonnegative-rational-numbers
open import elementary-number-theory.nonzero-natural-numbers
open import elementary-number-theory.positive-and-negative-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-natural-numbers
open import elementary-number-theory.strict-inequality-rational-numbers
open import elementary-number-theory.unit-fractions-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.images
open import foundation.propositional-truncations
open import foundation.subtypes
open import foundation.universe-levels

open import metric-spaces.approximations-metric-spaces
open import metric-spaces.metric-space-of-rational-numbers
open import metric-spaces.metric-spaces
open import metric-spaces.nets-metric-spaces
open import metric-spaces.subspaces-metric-spaces
open import metric-spaces.totally-bounded-metric-spaces
open import metric-spaces.totally-bounded-subspaces-metric-spaces

open import order-theory.posets

open import univalent-combinatorics.classical-finite-types
open import univalent-combinatorics.finitely-enumerable-subtypes
open import univalent-combinatorics.finitely-enumerable-types
```

</details>

## Idea

The
{{#concept "unit interval" Disambiguation="in the rational numbers" Agda=unit-closed-interval-ℚ}}
in the [rational numbers](elementary-number-theory.rational-numbers.md) is the
[closed interval](elementary-number-theory.closed-intervals-rational-numbers.md)
$[0, 1]$.

## Definition

```agda
unit-closed-interval-ℚ : closed-interval-ℚ
unit-closed-interval-ℚ = ( (zero-ℚ , one-ℚ) , leq-zero-one-ℚ)

subtype-unit-closed-interval-ℚ : subtype lzero ℚ
subtype-unit-closed-interval-ℚ =
  subtype-closed-interval-ℚ unit-closed-interval-ℚ

type-unit-closed-interval-ℚ : UU lzero
type-unit-closed-interval-ℚ = type-closed-interval-ℚ unit-closed-interval-ℚ

metric-space-unit-closed-interval-ℚ : Metric-Space lzero lzero
metric-space-unit-closed-interval-ℚ =
  subspace-Metric-Space metric-space-ℚ subtype-unit-closed-interval-ℚ
```

## Properties

### The partition of the unit interval into `n + 2` evenly spaced elements

```agda
module _
  (n : ℕ)
  where

  rational-partition-unit-closed-interval-ℚ : classical-Fin (n +ℕ 2) → ℚ
  rational-partition-unit-closed-interval-ℚ (k , k<n+2) =
    rational-ℕ k *ℚ reciprocal-rational-succ-ℕ n

  abstract
    is-nonnegative-rational-partition-unit-closed-interval-ℚ :
      (k : classical-Fin (n +ℕ 2)) →
      is-nonnegative-ℚ (rational-partition-unit-closed-interval-ℚ k)
    is-nonnegative-rational-partition-unit-closed-interval-ℚ (k , k<n+2) =
      is-nonnegative-mul-ℚ
        ( is-nonnegative-rational-ℕ k)
        ( is-nonnegative-rational-ℚ⁺ (positive-reciprocal-rational-succ-ℕ n))

    leq-one-rational-partition-unit-closed-interval-ℚ :
      (k : classical-Fin (n +ℕ 2)) →
      leq-ℚ (rational-partition-unit-closed-interval-ℚ k) one-ℚ
    leq-one-rational-partition-unit-closed-interval-ℚ (k , k<n+2) =
      let
        open inequality-reasoning-Poset ℚ-Poset
      in
        chain-of-inequalities
        rational-ℕ k *ℚ reciprocal-rational-succ-ℕ n
        ≤ rational-ℕ (succ-ℕ n) *ℚ reciprocal-rational-succ-ℕ n
          by
            preserves-leq-right-mul-ℚ⁺
              ( positive-reciprocal-rational-succ-ℕ n)
              ( rational-ℕ k)
              ( rational-ℕ (succ-ℕ n))
              ( preserves-leq-rational-ℕ (leq-le-succ-ℕ k (succ-ℕ n) k<n+2))
        ≤ one-ℚ
          by
            leq-eq-ℚ
              ( ap
                ( rational-ℚ⁺)
                ( right-inverse-law-mul-ℚ⁺
                  ( positive-rational-ℕ⁺ (succ-nonzero-ℕ' n))))

  element-partition-unit-closed-interval-ℚ :
    classical-Fin (n +ℕ 2) → type-unit-closed-interval-ℚ
  element-partition-unit-closed-interval-ℚ k =
    ( rational-partition-unit-closed-interval-ℚ k ,
      leq-zero-is-nonnegative-ℚ
        ( is-nonnegative-rational-partition-unit-closed-interval-ℚ k) ,
      leq-one-rational-partition-unit-closed-interval-ℚ k)

  subtype-partition-unit-closed-interval-ℚ :
    subtype lzero type-unit-closed-interval-ℚ
  subtype-partition-unit-closed-interval-ℚ =
    subtype-im element-partition-unit-closed-interval-ℚ

  abstract
    is-finitely-enumerable-subtype-partition-unit-closed-interval-ℚ :
      is-finitely-enumerable-subtype subtype-partition-unit-closed-interval-ℚ
    is-finitely-enumerable-subtype-partition-unit-closed-interval-ℚ =
      is-finitely-enumerable-im-Finitely-Enumerable-Type
        ( finitely-enumerable-type-Finite-Type
          ( finite-type-classical-Fin (n +ℕ 2)))
        ( element-partition-unit-closed-interval-ℚ)

  finitely-enumerable-subtype-partition-unit-closed-interval-ℚ :
    finitely-enumerable-subtype lzero type-unit-closed-interval-ℚ
  finitely-enumerable-subtype-partition-unit-closed-interval-ℚ =
    ( subtype-partition-unit-closed-interval-ℚ ,
      is-finitely-enumerable-subtype-partition-unit-closed-interval-ℚ)
```

### The division of `[0, 1]` into `n + 2` evenly spaced elements gives a `1/(n + 1)`-net on the metric space of `[0, 1]`

```agda
module _
  (n : ℕ)
  where

  abstract
    is-approximation-subtype-partition-unit-closed-interval-ℚ :
      is-approximation-Metric-Space
        ( metric-space-unit-closed-interval-ℚ)
        ( positive-reciprocal-rational-succ-ℕ n)
        ( subtype-partition-unit-closed-interval-ℚ n)
    is-approximation-subtype-partition-unit-closed-interval-ℚ
      (q , 0≤q , q≤1) =
      let
        q⁰⁺ = (q , is-nonnegative-leq-zero-ℚ 0≤q)
        k = nat-floor-ℚ⁰⁺ (q⁰⁺ *ℚ⁰⁺ nonnegative-rational-ℕ (succ-ℕ n))
        open inequality-reasoning-Poset ℚ-Poset
        1/n+1⁺@(1/n+1 , _) = positive-reciprocal-rational-succ-ℕ n
        k≤n+1 =
          reflects-leq-rational-ℕ
            ( k)
            ( succ-ℕ n)
            ( chain-of-inequalities
              rational-ℕ k
              ≤ q *ℚ rational-ℕ (succ-ℕ n)
                by leq-floor-ℚ⁰⁺ (q⁰⁺ *ℚ⁰⁺ nonnegative-rational-ℕ (succ-ℕ n))
              ≤ rational-ℕ (succ-ℕ n)
                by
                  is-deflationary-left-mul-leq-one-ℚ⁰⁺
                    ( q)
                    ( nonnegative-rational-ℕ (succ-ℕ n))
                    ( q≤1))
      in
        intro-exists
          ( map-unit-im
            ( element-partition-unit-closed-interval-ℚ n)
            ( k , le-succ-leq-ℕ k (succ-ℕ n) k≤n+1))
          ( ( chain-of-inequalities
              q
              ≤ (q *ℚ rational-ℕ (succ-ℕ n)) *ℚ 1/n+1
                by leq-eq-ℚ (inv (is-retraction-right-div-ℚ⁺ _ _))
              ≤ succ-ℚ (rational-ℕ k) *ℚ 1/n+1
                by
                  preserves-leq-right-mul-ℚ⁺
                    ( 1/n+1⁺)
                    ( q *ℚ rational-ℕ (succ-ℕ n))
                    ( succ-ℚ (rational-ℕ k))
                    ( leq-le-ℚ
                      ( le-succ-rational-floor-ℚ⁰⁺
                        ( q⁰⁺ *ℚ⁰⁺ nonnegative-rational-ℕ (succ-ℕ n))))
              ≤ rational-ℕ k *ℚ 1/n+1 +ℚ 1/n+1
                by leq-eq-ℚ (mul-left-succ-ℚ _ _ ∙ commutative-add-ℚ _ _)) ,
            ( chain-of-inequalities
              rational-ℕ k *ℚ 1/n+1
              ≤ (q *ℚ rational-ℕ (succ-ℕ n)) *ℚ 1/n+1
                by
                  preserves-leq-right-mul-ℚ⁺
                    ( positive-reciprocal-rational-succ-ℕ n)
                    ( rational-ℕ k)
                    ( q *ℚ rational-ℕ (succ-ℕ n))
                    ( leq-floor-ℚ⁰⁺
                      ( q⁰⁺ *ℚ⁰⁺ nonnegative-rational-ℕ (succ-ℕ n)))
              ≤ q
                by leq-eq-ℚ (is-retraction-right-div-ℚ⁺ _ _)
              ≤ q +ℚ 1/n+1
                by leq-right-add-rational-ℚ⁺ q 1/n+1⁺))
```

### `[0, 1]` is totally bounded as a metric space

```agda
abstract
  modulus-of-total-boundedness-unit-closed-interval-ℚ :
    (ε : ℚ⁺) → net-Metric-Space lzero metric-space-unit-closed-interval-ℚ ε
  modulus-of-total-boundedness-unit-closed-interval-ℚ ε
    with smaller-reciprocal-ℚ⁺ ε
  ... | ((0 , H) , _) = ex-falso (H refl)
  ... | ((succ-ℕ n , _) , ε<1/n+1) =
    ( finitely-enumerable-subtype-partition-unit-closed-interval-ℚ n ,
      is-approximation-is-approximation-leq-Metric-Space
        ( metric-space-unit-closed-interval-ℚ)
        ( positive-reciprocal-rational-succ-ℕ n)
        ( ε)
        ( leq-le-ℚ ε<1/n+1)
        ( subtype-partition-unit-closed-interval-ℚ n)
        ( is-approximation-subtype-partition-unit-closed-interval-ℚ n))

  is-totally-bounded-unit-closed-interval-ℚ :
    is-totally-bounded-Metric-Space lzero metric-space-unit-closed-interval-ℚ
  is-totally-bounded-unit-closed-interval-ℚ =
    unit-trunc-Prop modulus-of-total-boundedness-unit-closed-interval-ℚ

totally-bounded-subspace-unit-closed-interval-ℚ :
  totally-bounded-subspace-Metric-Space lzero lzero metric-space-ℚ
totally-bounded-subspace-unit-closed-interval-ℚ =
  ( subtype-unit-closed-interval-ℚ ,
    is-totally-bounded-unit-closed-interval-ℚ)
```
