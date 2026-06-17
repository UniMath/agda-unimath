# Scalar multiplication of differentiable maps from proper closed intervals in ℝ to a normed real vector space

```agda
module functional-analysis.scalar-multiplication-differentiable-maps-on-proper-closed-intervals-real-numbers-normed-real-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.multiplication-positive-rational-numbers
open import elementary-number-theory.multiplicative-group-of-positive-rational-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.universe-levels

open import functional-analysis.differentiable-maps-on-proper-closed-intervals-real-numbers-normed-real-vector-spaces

open import linear-algebra.normed-real-vector-spaces

open import order-theory.large-posets

open import real-numbers.absolute-value-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.distance-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.multiplication-nonnegative-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.proper-closed-intervals-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.strict-inequality-real-numbers
```

</details>

## Idea

Given a [normed real vector space](linear-algebra.normed-real-vector-spaces.md)
`V`, a
[proper closed interval](real-numbers.proper-closed-intervals-real-numbers.md)
of [real numbers](real-numbers.dedekind-real-numbers.md) `[a, b]`, a real number
`c`, and a
[differentiable](functional-analysis.differentiable-maps-on-proper-closed-intervals-real-numbers-normed-real-vector-spaces.md)
map `f : [a, b] → V` with derivative `f'`, the map `x ↦ c * f x` is
differentiable with derivative `x ↦ c * f' x`.

## Proof

```agda
module _
  {l1 l2 : Level}
  (V : Normed-ℝ-Vector-Space l1 l2)
  ([a,b] : proper-closed-interval-ℝ l1 l1)
  (c : ℝ l1)
  (df@(f , f' , Df) :
    differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
      ( V)
      ( [a,b]))
  where

  map-scalar-mul-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space :
    type-proper-closed-interval-ℝ l1 [a,b] → type-Normed-ℝ-Vector-Space V
  map-scalar-mul-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
    x =
    mul-Normed-ℝ-Vector-Space V c (f x)

  map-derivative-scalar-mul-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space :
    type-proper-closed-interval-ℝ l1 [a,b] → type-Normed-ℝ-Vector-Space V
  map-derivative-scalar-mul-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
    x =
    mul-Normed-ℝ-Vector-Space V c (f' x)

  abstract
    is-derivative-map-derivative-scalar-mul-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space :
      is-derivative-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
        ( V)
        ( [a,b])
        ( map-scalar-mul-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space)
        ( map-derivative-scalar-mul-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space)
    is-derivative-map-derivative-scalar-mul-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space =
      let
        open
          do-syntax-trunc-Prop
            ( is-derivative-prop-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
              ( V)
              ( [a,b])
              ( map-scalar-mul-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space)
              ( map-derivative-scalar-mul-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space))
        open inequality-reasoning-Large-Poset ℝ-Large-Poset
        dist-V = dist-Normed-ℝ-Vector-Space V
        norm-V = norm-Normed-ℝ-Vector-Space V
        _*V_ = mul-Normed-ℝ-Vector-Space V
        _-V_ = diff-Normed-ℝ-Vector-Space V
      in do
        (q , |c|<q) ← exists-greater-positive-rational-ℝ (abs-ℝ c)
        (μf , is-mod-μf) ← Df
        let μcf ε = μf (inv-ℚ⁺ q *ℚ⁺ ε)
        intro-exists
          ( μcf)
          ( λ ε x@(xℝ , _) y@(yℝ , _) Nδxy →
            chain-of-inequalities
              dist-V ((c *V f y) -V (c *V f x)) ((yℝ -ℝ xℝ) *V (c *V f' x))
              ≤ dist-V (c *V (f y -V f x)) (c *V ((yℝ -ℝ xℝ) *V f' x))
                by
                  leq-eq-ℝ
                    ( ap-binary
                      ( dist-V)
                      ( inv
                        ( left-distributive-mul-diff-Normed-ℝ-Vector-Space V
                          ( c)
                          ( f y)
                          ( f x)))
                      ( left-swap-mul-Normed-ℝ-Vector-Space V _ _ _))
              ≤ abs-ℝ c *ℝ dist-V (f y -V f x) ((yℝ -ℝ xℝ) *V f' x)
                by
                  leq-eq-ℝ
                    ( inv
                      ( left-distributive-abs-mul-dist-Normed-ℝ-Vector-Space V
                        ( _)
                        ( _)
                        ( _)))
              ≤ real-ℚ⁺ q *ℝ (real-ℚ⁺ (inv-ℚ⁺ q *ℚ⁺ ε) *ℝ dist-ℝ yℝ xℝ)
                by
                  preserves-leq-mul-ℝ⁰⁺
                    ( nonnegative-abs-ℝ c)
                    ( nonnegative-real-ℚ⁺ q)
                    ( nonnegative-norm-Normed-ℝ-Vector-Space V _)
                    ( nonnegative-real-ℚ⁺ (inv-ℚ⁺ q *ℚ⁺ ε) *ℝ⁰⁺
                      nonnegative-dist-ℝ yℝ xℝ)
                    ( leq-le-ℝ |c|<q)
                    ( is-mod-μf (inv-ℚ⁺ q *ℚ⁺ ε) x y Nδxy)
              ≤ (real-ℚ⁺ q *ℝ real-ℚ⁺ (inv-ℚ⁺ q *ℚ⁺ ε)) *ℝ dist-ℝ yℝ xℝ
                by leq-eq-ℝ (inv (associative-mul-ℝ _ _ _))
              ≤ real-ℚ⁺ (q *ℚ⁺ (inv-ℚ⁺ q *ℚ⁺ ε)) *ℝ dist-ℝ yℝ xℝ
                by leq-eq-ℝ (ap-mul-ℝ (mul-real-ℚ _ _) refl)
              ≤ real-ℚ⁺ ε *ℝ dist-ℝ yℝ xℝ
                by
                  leq-eq-ℝ
                    ( ap-mul-ℝ (ap real-ℚ (is-section-left-div-ℚ⁺ q _)) refl))

  is-differentiable-map-scalar-mul-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space :
    is-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
      ( V)
      ( [a,b])
      ( map-scalar-mul-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space)
  is-differentiable-map-scalar-mul-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space =
    ( map-derivative-scalar-mul-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space ,
      is-derivative-map-derivative-scalar-mul-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space)

  scalar-mul-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space :
    differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
      ( V)
      ( [a,b])
  scalar-mul-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space =
    ( map-scalar-mul-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space ,
      is-differentiable-map-scalar-mul-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space)
```
