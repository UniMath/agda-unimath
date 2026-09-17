# The differentiability of constant maps from proper closed intervals in ℝ to normed real vector spaces

```agda
module functional-analysis.differentiability-constant-maps-on-proper-closed-intervals-real-numbers-normed-real-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.constant-maps
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.universe-levels

open import functional-analysis.differentiable-maps-on-proper-closed-intervals-real-numbers-normed-real-vector-spaces

open import linear-algebra.normed-real-vector-spaces

open import order-theory.large-posets

open import real-numbers.difference-real-numbers
open import real-numbers.distance-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.multiplication-nonnegative-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.proper-closed-intervals-real-numbers
open import real-numbers.raising-universe-levels-real-numbers
open import real-numbers.rational-real-numbers
```

</details>

## Idea

[Constant maps](foundation.constant-maps.md) from a
[proper closed interval](real-numbers.proper-closed-intervals-real-numbers.md)
in the [real numbers](real-numbers.dedekind-real-numbers.md) to a
[normed real vector space](linear-algebra.normed-real-vector-spaces.md) are
always
[differentiable](functional-analysis.differentiable-maps-on-proper-closed-intervals-real-numbers-normed-real-vector-spaces.md)
with derivative zero.

## Proof

```agda
module _
  {l1 l2 : Level}
  (V : Normed-ℝ-Vector-Space l1 l2)
  ([a,b] : proper-closed-interval-ℝ l1 l1)
  (v : type-Normed-ℝ-Vector-Space V)
  where

  abstract
    is-derivative-zero-const-map-proper-closed-interval-real-Normed-ℝ-Vector-Space :
      is-derivative-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
        ( V)
        ( [a,b])
        ( const (type-proper-closed-interval-ℝ l1 [a,b]) v)
        ( const
          ( type-proper-closed-interval-ℝ l1 [a,b])
          ( zero-Normed-ℝ-Vector-Space V))
    is-derivative-zero-const-map-proper-closed-interval-real-Normed-ℝ-Vector-Space =
      let
        open inequality-reasoning-Large-Poset ℝ-Large-Poset
        dist-V = dist-Normed-ℝ-Vector-Space V
        norm-V = map-norm-Normed-ℝ-Vector-Space V
        _-V_ = diff-Normed-ℝ-Vector-Space V
        _*V_ = mul-Normed-ℝ-Vector-Space V
        0V = zero-Normed-ℝ-Vector-Space V
      in
        intro-exists
          ( λ _ → one-ℚ⁺)
          ( λ ε x@(xℝ , _) y@(yℝ , _) _ →
            chain-of-inequalities
              dist-V (v -V v) ((yℝ -ℝ xℝ) *V 0V)
              ≤ dist-V 0V 0V
                by
                  leq-eq-ℝ
                    ( ap-binary
                      ( dist-V)
                      ( right-inverse-law-add-Normed-ℝ-Vector-Space V v)
                      ( right-zero-law-mul-Normed-ℝ-Vector-Space V _))
              ≤ zero-ℝ
                by leq-sim-ℝ (refl-dist-Normed-ℝ-Vector-Space V 0V)
              ≤ real-ℚ⁺ ε *ℝ dist-ℝ yℝ xℝ
                by
                  is-nonnegative-real-ℝ⁰⁺
                    ( nonnegative-real-ℚ⁺ ε *ℝ⁰⁺ nonnegative-dist-ℝ yℝ xℝ))

  is-differentiable-const-map-proper-closed-interval-real-Normed-ℝ-Vector-Space :
    is-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
      ( V)
      ( [a,b])
      ( const (type-proper-closed-interval-ℝ l1 [a,b]) v)
  is-differentiable-const-map-proper-closed-interval-real-Normed-ℝ-Vector-Space =
    ( const
        ( type-proper-closed-interval-ℝ l1 [a,b])
        ( zero-Normed-ℝ-Vector-Space V) ,
      is-derivative-zero-const-map-proper-closed-interval-real-Normed-ℝ-Vector-Space)

  differentiable-const-map-proper-closed-interval-real-Normed-ℝ-Vector-Space :
    differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
      ( V)
      ( [a,b])
  differentiable-const-map-proper-closed-interval-real-Normed-ℝ-Vector-Space =
    ( const
        ( type-proper-closed-interval-ℝ l1 [a,b])
        ( v) ,
      is-differentiable-const-map-proper-closed-interval-real-Normed-ℝ-Vector-Space)
```
