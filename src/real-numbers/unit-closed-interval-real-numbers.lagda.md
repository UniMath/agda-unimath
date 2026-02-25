# The unit closed interval in the real numbers

```agda
{-# OPTIONS --lossy-unification #-}
module real-numbers.unit-closed-interval-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.unit-closed-interval-rational-numbers

open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.images
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.complete-metric-spaces
open import metric-spaces.metric-spaces

open import real-numbers.closed-intervals-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.density-rationals-proper-closed-intervals-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.proper-closed-intervals-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.strict-inequality-real-numbers
open import real-numbers.subsets-real-numbers
open import real-numbers.totally-bounded-subsets-real-numbers

open import univalent-combinatorics.finitely-enumerable-subtypes
```

</details>

## Idea

The
{{#concept "unit interval" WDID=Q1987578 WD="unit interval" Disambiguation="in the real numbers" Agda=unit-closed-interval-ℝ}}
in the [real numbers](real-numbers.dedekind-real-numbers.md) is the
[proper closed interval](real-numbers.proper-closed-intervals-real-numbers.md)
`[0, 1]`.

## Definition

```agda
unit-proper-closed-interval-ℝ : proper-closed-interval-ℝ lzero lzero
unit-proper-closed-interval-ℝ =
  ( zero-ℝ , one-ℝ , le-zero-one-ℝ)

unit-closed-interval-ℝ : closed-interval-ℝ lzero lzero
unit-closed-interval-ℝ =
  ( (zero-ℝ , one-ℝ) , leq-zero-one-ℝ)

subset-unit-interval-ℝ : (l : Level) → subset-ℝ l l
subset-unit-interval-ℝ l = subtype-closed-interval-ℝ l unit-closed-interval-ℝ

type-unit-interval-ℝ : (l : Level) → UU (lsuc l)
type-unit-interval-ℝ l = type-subtype (subset-unit-interval-ℝ l)
```

## Properties

### The metric space associated with the unit closed interval

```agda
metric-space-unit-interval-ℝ :
  (l : Level) → Metric-Space (lsuc l) l
metric-space-unit-interval-ℝ l =
  metric-space-closed-interval-ℝ l unit-closed-interval-ℝ

complete-metric-space-unit-interval-ℝ :
  (l : Level) → Complete-Metric-Space (lsuc l) l
complete-metric-space-unit-interval-ℝ l =
  complete-metric-space-closed-interval-ℝ l unit-closed-interval-ℝ
```

### The unit closed interval is totally bounded

```agda
module _
  (l : Level)
  where

  abstract
    modulus-of-total-boundedness-unit-closed-interval-ℝ :
      modulus-of-total-boundedness-subset-ℝ
        ( lsuc l)
        ( subset-unit-interval-ℝ l)
    modulus-of-total-boundedness-unit-closed-interval-ℝ ε =
      let
        (ε₁ , ε₂ , ε₁+ε₂=ε) = split-ℚ⁺ ε
        (S , is-net-S) =
          modulus-of-total-boundedness-unit-closed-interval-ℚ ε₁
      in
        ( im-finitely-enumerable-subtype
            ( raise-real-type-closed-interval-ℚ l unit-closed-interval-ℚ)
            ( S) ,
          λ (x , 0≤x , x≤1) →
            let
              open
                do-syntax-trunc-Prop
                  ( ∃
                    ( type-im-finitely-enumerable-subtype
                      ( raise-real-type-closed-interval-ℚ
                        ( l)
                        ( unit-closed-interval-ℚ))
                      ( S))
                    ( λ ((y , _) , _) → neighborhood-prop-ℝ l ε y x))
            in do
              ((pℝ , 0≤pℝ , pℝ≤1) , Nε₂xp , p , p=pℝ) ←
                is-dense-subset-rational-proper-closed-interval-ℝ
                  ( l)
                  ( unit-proper-closed-interval-ℝ)
                  ( x , 0≤x , x≤1)
                  ( ε₂)
              (((q , 0≤q , q≤1) , q∈S) , Nε₁qp) ←
                is-net-S
                  ( p ,
                    reflects-leq-real-ℚ
                      ( preserves-leq-right-sim-ℝ
                        ( sim-rational-ℝ (pℝ , p , p=pℝ))
                        ( 0≤pℝ)) ,
                    reflects-leq-real-ℚ
                      ( preserves-leq-left-sim-ℝ
                        ( sim-rational-ℝ (pℝ , p , p=pℝ))
                        ( pℝ≤1)))
              intro-exists
                ( map-unit-im
                  ( ( raise-real-type-closed-interval-ℚ
                      ( l)
                      ( unit-closed-interval-ℚ)) ∘
                    ( pr1))
                  ( (q , 0≤q , q≤1) , q∈S))
                ( tr
                  ( λ δ → neighborhood-ℝ l δ (raise-real-ℚ l q) x)
                  ( ε₁+ε₂=ε)
                  ( is-triangular-neighborhood-ℝ
                    ( raise-real-ℚ l q)
                    ( pℝ)
                    ( x)
                    ( ε₁)
                    ( ε₂)
                    ( is-symmetric-neighborhood-ℝ ε₂ x pℝ Nε₂xp)
                    ( inv-tr
                      ( neighborhood-ℝ l ε₁ (raise-real-ℚ l q))
                      ( eq-raise-real-rational-is-rational-ℝ p=pℝ)
                      ( forward-implication
                        ( is-isometry-raise-real-ℚ
                          ( l)
                          ( ε₁)
                          ( q)
                          ( p))
                        ( Nε₁qp))))))

    is-totally-bounded-unit-closed-interval-ℝ :
      is-totally-bounded-subset-ℝ
        ( lsuc l)
        ( subset-unit-interval-ℝ l)
    is-totally-bounded-unit-closed-interval-ℝ =
      unit-trunc-Prop modulus-of-total-boundedness-unit-closed-interval-ℝ
```
