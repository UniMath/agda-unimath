# Addition of differentiable maps from proper closed intervals in ℝ to normed real vector spaces

```agda
module functional-analysis.addition-differentiable-maps-on-proper-closed-intervals-real-numbers-normed-real-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.minimum-positive-rational-numbers

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

open import real-numbers.addition-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.distance-real-numbers
open import real-numbers.inequalities-addition-and-subtraction-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.proper-closed-intervals-real-numbers
open import real-numbers.rational-real-numbers
```

</details>

## Idea

Given a
[proper closed interval in the real numbers](real-numbers.proper-closed-intervals-real-numbers.md)
`[a, b]`, a
[normed real vector space](linear-algebra.normed-real-vector-spaces.md) `V`, and
two
[differentiable maps](functional-analysis.differentiable-maps-on-proper-closed-intervals-real-numbers-normed-real-vector-spaces.md)
`f g : [a, b] → V` with derivatives `f'` and `g'`, the map `x ↦ f x + g x` is
differentiable with derivative `x ↦ f' x + g' x`.

## Proof

```agda
module _
  {l1 l2 : Level}
  (V : Normed-ℝ-Vector-Space l1 l2)
  ([a,b] : proper-closed-interval-ℝ l1 l1)
  ( df@(f , f' , Df)
    dg@(g , g' , Dg) :
      differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
        ( V)
        ( [a,b]))
  where

  map-add-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space :
    type-proper-closed-interval-ℝ l1 [a,b] → type-Normed-ℝ-Vector-Space V
  map-add-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
    x =
    add-Normed-ℝ-Vector-Space V (f x) (g x)

  map-derivative-add-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space :
    type-proper-closed-interval-ℝ l1 [a,b] → type-Normed-ℝ-Vector-Space V
  map-derivative-add-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
    x =
    add-Normed-ℝ-Vector-Space V (f' x) (g' x)

  abstract
    is-derivative-map-derivative-add-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space :
      is-derivative-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
        ( V)
        ( [a,b])
        ( map-add-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space)
        ( map-derivative-add-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space)
    is-derivative-map-derivative-add-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space =
      let
        open
          do-syntax-trunc-Prop
            ( is-derivative-prop-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
              ( V)
              ( [a,b])
              ( map-add-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space)
              ( map-derivative-add-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space))
        open inequality-reasoning-Large-Poset ℝ-Large-Poset
        dist-V = dist-Normed-ℝ-Vector-Space V
        norm-V = map-norm-Normed-ℝ-Vector-Space V
        _-V_ = diff-Normed-ℝ-Vector-Space V
        _*V_ = mul-Normed-ℝ-Vector-Space V
        _+V_ = add-Normed-ℝ-Vector-Space V
      in do
        (μf , is-mod-μf) ← Df
        (μg , is-mod-μg) ← Dg
        let
          μf+g ε =
            let (εf , εg , εf+εg=ε) = split-ℚ⁺ ε in min-ℚ⁺ (μf εf) (μg εg)
        intro-exists
          ( μf+g)
          ( λ ε x@(xℝ , _) y@(yℝ , _) Nδxy →
            let
              (εf , εg , εf+εg=ε) = split-ℚ⁺ ε
            in
              chain-of-inequalities
                dist-V
                  ( (f y +V g y) -V (f x +V g x))
                  ( (yℝ -ℝ xℝ) *V (f' x +V g' x))
                ≤
                  dist-V
                    ( (f y -V f x) +V (g y -V g x))
                    ( ((yℝ -ℝ xℝ) *V f' x) +V ((yℝ -ℝ xℝ) *V g' x))
                  by
                    leq-eq-ℝ
                      ( ap-binary
                        ( dist-V)
                        ( interchange-add-diff-Normed-ℝ-Vector-Space V _ _ _ _)
                        ( left-distributive-mul-add-Normed-ℝ-Vector-Space V
                          ( _)
                          ( _)
                          ( _)))
                ≤ norm-V
                    ( ((f y -V f x) -V ((yℝ -ℝ xℝ) *V f' x)) +V
                      ((g y -V g x) -V ((yℝ -ℝ xℝ) *V g' x)))
                  by
                    leq-eq-ℝ
                      ( ap
                        ( norm-V)
                        ( interchange-add-diff-Normed-ℝ-Vector-Space V _ _ _ _))
                ≤ dist-V (f y -V f x) ((yℝ -ℝ xℝ) *V f' x) +ℝ
                  dist-V (g y -V g x) ((yℝ -ℝ xℝ) *V g' x)
                  by triangular-norm-Normed-ℝ-Vector-Space V _ _
                ≤ real-ℚ⁺ εf *ℝ dist-ℝ yℝ xℝ +ℝ
                  real-ℚ⁺ εg *ℝ dist-ℝ yℝ xℝ
                  by
                    preserves-leq-add-ℝ
                      ( is-mod-μf
                        ( εf)
                        ( x)
                        ( y)
                        ( weakly-monotonic-neighborhood-ℝ
                          ( xℝ)
                          ( yℝ)
                          ( μf+g ε)
                          ( μf εf)
                          ( leq-left-min-ℚ⁺ (μf εf) (μg εg))
                          ( Nδxy)))
                      ( is-mod-μg
                        ( εg)
                        ( x)
                        ( y)
                        ( weakly-monotonic-neighborhood-ℝ
                          ( xℝ)
                          ( yℝ)
                          ( μf+g ε)
                          ( μg εg)
                          ( leq-right-min-ℚ⁺ (μf εf) (μg εg))
                          ( Nδxy)))
                ≤ (real-ℚ⁺ εf +ℝ real-ℚ⁺ εg) *ℝ dist-ℝ yℝ xℝ
                  by leq-eq-ℝ (inv (right-distributive-mul-add-ℝ _ _ _))
                ≤ real-ℚ⁺ (εf +ℚ⁺ εg) *ℝ dist-ℝ yℝ xℝ
                  by leq-eq-ℝ (ap-mul-ℝ (add-real-ℚ _ _) refl)
                ≤ real-ℚ⁺ ε *ℝ dist-ℝ yℝ xℝ
                  by leq-eq-ℝ (ap-mul-ℝ (ap real-ℚ⁺ εf+εg=ε) refl))

  is-differentiable-map-add-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space :
    is-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space
      ( V)
      ( [a,b])
      ( map-add-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space)
  is-differentiable-map-add-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space =
    ( map-derivative-add-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space ,
      is-derivative-map-derivative-add-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space)

  add-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space :
    differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space V [a,b]
  add-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space =
    ( map-add-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space ,
      is-differentiable-map-add-differentiable-map-proper-closed-interval-real-Normed-ℝ-Vector-Space)
```
