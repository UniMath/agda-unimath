# The differentiability of the reciprocal function on proper closed intervals in the real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module analysis.differentiability-reciprocal-function-on-positive-proper-closed-intervals-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import analysis.differentiable-real-functions-on-proper-closed-intervals-real-numbers

open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.minimum-positive-rational-numbers
open import elementary-number-theory.multiplication-positive-rational-numbers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.multiplicative-group-of-positive-rational-numbers
open import elementary-number-theory.powers-positive-rational-numbers
open import elementary-number-theory.squares-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.universe-levels

open import order-theory.large-posets

open import real-numbers.absolute-value-real-numbers
open import real-numbers.addition-real-numbers
open import real-numbers.binary-maximum-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.distance-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.multiplication-nonnegative-real-numbers
open import real-numbers.multiplication-positive-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.multiplicative-inverses-positive-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.positive-and-negative-real-numbers
open import real-numbers.positive-proper-closed-intervals-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.proper-closed-intervals-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-real-numbers
open import real-numbers.squares-real-numbers
open import real-numbers.strict-inequality-real-numbers
```

</details>

## Idea

On a [positive](real-numbers.positive-proper-closed-intervals-real-numbers.md)
[proper closed interval](real-numbers.proper-closed-intervals-real-numbers.md)
in the [real numbers](real-numbers.dedekind-real-numbers.md), the
[multiplicative inverse function](real-numbers.multiplicative-inverses-positive-real-numbers.md)
is
[differentiable](analysis.differentiable-real-functions-on-proper-closed-intervals-real-numbers.md)
with derivative $$x ↦ -\frac{1}{x^2}$$

## Proof

```agda
module _
  {l : Level}
  ([a,b] : proper-closed-interval-ℝ l l)
  (0<a : is-positive-proper-closed-interval-ℝ [a,b])
  where

  positive-map-inv-type-is-positive-proper-closed-interval-ℝ :
    type-proper-closed-interval-ℝ l [a,b] → ℝ⁺ l
  positive-map-inv-type-is-positive-proper-closed-interval-ℝ =
    inv-ℝ⁺ ∘ positive-real-type-is-positive-proper-closed-interval-ℝ [a,b] 0<a

  map-inv-type-is-positive-proper-closed-interval-ℝ :
    type-proper-closed-interval-ℝ l [a,b] → ℝ l
  map-inv-type-is-positive-proper-closed-interval-ℝ =
    real-ℝ⁺ ∘ positive-map-inv-type-is-positive-proper-closed-interval-ℝ

  map-derivative-inv-type-is-positive-proper-closed-interval-ℝ :
    type-proper-closed-interval-ℝ l [a,b] → ℝ l
  map-derivative-inv-type-is-positive-proper-closed-interval-ℝ =
    neg-ℝ ∘ square-ℝ ∘ map-inv-type-is-positive-proper-closed-interval-ℝ

  abstract
    is-derivative-inv-type-is-positive-proper-closed-interval-ℝ :
      is-derivative-real-function-proper-closed-interval-ℝ
        ( [a,b])
        ( map-inv-type-is-positive-proper-closed-interval-ℝ)
        ( map-derivative-inv-type-is-positive-proper-closed-interval-ℝ)
    is-derivative-inv-type-is-positive-proper-closed-interval-ℝ =
      let
        open
          do-syntax-trunc-Prop
            ( is-derivative-prop-real-function-proper-closed-interval-ℝ
              ( [a,b])
              ( map-inv-type-is-positive-proper-closed-interval-ℝ)
              ( map-derivative-inv-type-is-positive-proper-closed-interval-ℝ))
        open inequality-reasoning-Large-Poset ℝ-Large-Poset
        pos-type-[a,b] =
          positive-real-type-is-positive-proper-closed-interval-ℝ [a,b] 0<a
        real-inv-type-[a,b] =
          map-inv-type-is-positive-proper-closed-interval-ℝ
        pos-inv-type-[a,b] =
          positive-map-inv-type-is-positive-proper-closed-interval-ℝ
        (a , b , a<b) = [a,b]
        K = max-ℝ (real-inv-ℝ⁺ (a , 0<a)) b
      in do
        (M⁺@(M , _) , K<M) ← exists-greater-positive-rational-ℝ K
        let
          real-inv-type-[a,b]<M x =
            concatenate-leq-le-ℝ _ _ _
              ( inv-leq-ℝ⁺ (a , 0<a) (pos-type-[a,b] x) (pr1 (pr2 x)))
              ( concatenate-leq-le-ℝ _ K _
                ( leq-left-max-ℝ (real-inv-ℝ⁺ (a , 0<a)) b)
                ( K<M))
          M⁻³ = inv-ℚ⁺ (power-ℚ⁺ 3 M⁺)
        intro-exists
          ( mul-ℚ⁺ M⁻³)
          ( λ ε x y Nδxy →
            chain-of-inequalities
              dist-ℝ
                ( real-inv-type-[a,b] y -ℝ real-inv-type-[a,b] x)
                ( ( neg-ℝ (square-ℝ (real-inv-type-[a,b] x))) *ℝ
                  ( pr1 y -ℝ pr1 x))
              ≤ ( real-inv-ℝ⁺ (pos-type-[a,b] x *ℝ⁺ pos-type-[a,b] y)) *ℝ
                ( dist-ℝ
                  ( ( pr1 x *ℝ pr1 y) *ℝ
                    ( real-inv-type-[a,b] y -ℝ real-inv-type-[a,b] x))
                  ( ( pr1 x *ℝ pr1 y) *ℝ
                    ( ( neg-ℝ (square-ℝ (real-inv-type-[a,b] x))) *ℝ
                      ( pr1 y -ℝ pr1 x))))
                by
                  leq-sim-ℝ'
                    ( cancel-left-div-mul-dist-ℝ⁺
                      ( pos-type-[a,b] x *ℝ⁺ pos-type-[a,b] y)
                      ( _)
                      ( _))
              ≤ ( ( real-inv-ℝ⁺ (pos-type-[a,b] x)) *ℝ
                  ( real-inv-ℝ⁺ (pos-type-[a,b] y))) *ℝ
                ( dist-ℝ
                  ( ( (pr1 x *ℝ pr1 y) *ℝ real-inv-type-[a,b] y) -ℝ
                    ( (pr1 x *ℝ pr1 y) *ℝ real-inv-type-[a,b] x))
                  ( ( pr1 x *ℝ pr1 y) *ℝ
                    ( ( square-ℝ (real-inv-type-[a,b] x)) *ℝ
                      ( neg-ℝ (pr1 y -ℝ pr1 x)))))
                by
                  leq-eq-ℝ
                    ( ap-mul-ℝ
                      ( distributive-real-inv-mul-ℝ⁺ _ _)
                      ( ap-dist-ℝ
                        ( left-distributive-mul-diff-ℝ _ _ _)
                        ( ap-mul-ℝ
                          ( refl)
                          ( ( left-negative-law-mul-ℝ _ _) ∙
                            ( inv (right-negative-law-mul-ℝ _ _))))))
              ≤ ( square-ℝ (real-ℚ M)) *ℝ
                ( dist-ℝ
                  ( ( ( pr1 x *ℝ pr1 y) *ℝ real-inv-type-[a,b] y) -ℝ
                    ( ( pr1 y *ℝ pr1 x) *ℝ real-inv-type-[a,b] x))
                  ( ( pr1 x *ℝ pr1 y) *ℝ
                    ( ( square-ℝ (real-inv-type-[a,b] x)) *ℝ
                      ( pr1 x -ℝ pr1 y))))
                by
                  preserves-leq-mul-ℝ⁰⁺
                    ( nonnegative-ℝ⁺
                      ( ( inv-ℝ⁺ (pos-type-[a,b] x)) *ℝ⁺
                        ( inv-ℝ⁺ (pos-type-[a,b] y))))
                    ( nonnegative-square-ℝ _)
                    ( nonnegative-dist-ℝ _ _)
                    ( nonnegative-dist-ℝ _ _)
                    ( preserves-leq-mul-ℝ⁰⁺
                      ( nonnegative-ℝ⁺ (inv-ℝ⁺ (pos-type-[a,b] x)))
                      ( nonnegative-real-ℚ⁺ M⁺)
                      ( nonnegative-ℝ⁺ (inv-ℝ⁺ (pos-type-[a,b] y)))
                      ( nonnegative-real-ℚ⁺ M⁺)
                      ( leq-le-ℝ (real-inv-type-[a,b]<M x))
                      ( leq-le-ℝ (real-inv-type-[a,b]<M y)))
                    ( leq-eq-ℝ
                      ( ap-dist-ℝ
                        ( ap-diff-ℝ
                          ( refl)
                          ( ap-mul-ℝ (commutative-mul-ℝ _ _) refl))
                        ( ap-mul-ℝ
                          ( refl)
                          ( ap-mul-ℝ refl (distributive-neg-diff-ℝ _ _)))))
              ≤ ( square-ℝ (real-ℚ M)) *ℝ
                ( dist-ℝ
                  ( pr1 x -ℝ pr1 y)
                  ( ( pr1 x *ℝ square-ℝ (real-inv-type-[a,b] x)) *ℝ
                    ( pr1 y *ℝ (pr1 x -ℝ pr1 y))))
                by
                  leq-eq-ℝ
                    ( ap-mul-ℝ
                      ( refl)
                      ( ap-dist-ℝ
                        ( ap-diff-ℝ
                          ( eq-sim-ℝ (cancel-right-mul-div-ℝ⁺ _ _))
                          ( eq-sim-ℝ (cancel-right-mul-div-ℝ⁺ _ _)))
                        ( interchange-law-mul-mul-ℝ _ _ _ _)))
              ≤ ( square-ℝ (real-ℚ M)) *ℝ
                ( dist-ℝ
                  ( pr1 x -ℝ pr1 y)
                  ( ( real-inv-type-[a,b] x) *ℝ
                    ( pr1 y *ℝ (pr1 x -ℝ pr1 y))))
                by
                  leq-eq-ℝ
                    ( ap-mul-ℝ
                      ( refl)
                      ( ap-dist-ℝ
                        ( refl)
                        ( ap-mul-ℝ
                          ( eq-sim-ℝ (cancel-left-mul-div-ℝ⁺ _ _))
                          ( refl))))
              ≤ ( square-ℝ (real-ℚ M)) *ℝ
                ( dist-ℝ
                  ( one-ℝ *ℝ (pr1 x -ℝ pr1 y))
                  ( (real-inv-type-[a,b] x *ℝ pr1 y) *ℝ (pr1 x -ℝ pr1 y)))
                by
                  leq-eq-ℝ
                    ( ap-mul-ℝ
                      ( refl)
                      ( ap-dist-ℝ
                        ( inv (left-unit-law-mul-ℝ _))
                        ( inv (associative-mul-ℝ _ _ _))))
              ≤ ( square-ℝ (real-ℚ M)) *ℝ
                ( ( dist-ℝ one-ℝ (real-inv-type-[a,b] x *ℝ pr1 y)) *ℝ
                  ( dist-ℝ (pr1 x) (pr1 y)))
                by
                  leq-eq-ℝ
                    ( ap-mul-ℝ
                      ( refl)
                      ( inv (right-distributive-abs-mul-dist-ℝ _ _ _)))
              ≤ ( square-ℝ (real-ℚ M)) *ℝ
                ( ( ( real-inv-type-[a,b] x) *ℝ
                    ( dist-ℝ
                      ( pr1 x *ℝ one-ℝ)
                      ( pr1 x *ℝ (real-inv-type-[a,b] x *ℝ pr1 y)))) *ℝ
                  ( dist-ℝ (pr1 x) (pr1 y)))
                by
                  leq-eq-ℝ
                    ( ap-mul-ℝ
                      ( refl)
                      ( ap-mul-ℝ
                        ( inv
                          ( eq-sim-ℝ
                            ( cancel-left-div-mul-dist-ℝ⁺
                              ( pos-type-[a,b] x)
                              ( one-ℝ)
                              ( real-inv-type-[a,b] x *ℝ pr1 y))))
                        ( refl)))
              ≤ ( real-ℚ (square-ℚ M)) *ℝ
                ( ( real-inv-type-[a,b] x) *ℝ
                  ( dist-ℝ (pr1 x) (pr1 y)) *ℝ
                  ( dist-ℝ (pr1 x) (pr1 y)))
                by
                  leq-eq-ℝ
                    ( ap-mul-ℝ
                      ( mul-real-ℚ _ _)
                      ( ap-mul-ℝ
                        ( ap-mul-ℝ
                          ( refl)
                          ( ap-dist-ℝ
                            ( right-unit-law-mul-ℝ (pr1 x))
                            ( eq-sim-ℝ (cancel-left-mul-div-ℝ⁺ _ _))))
                        ( refl)))
              ≤ ( real-ℚ (square-ℚ M)) *ℝ
                ( ( real-ℚ M) *ℝ
                  ( real-ℚ⁺ (M⁻³ *ℚ⁺ ε)) *ℝ
                  ( dist-ℝ (pr1 x) (pr1 y)))
                by
                  preserves-leq-left-mul-ℝ⁰⁺
                    ( nonnegative-real-ℚ⁰⁺ (nonnegative-square-ℚ M))
                    ( preserves-leq-right-mul-ℝ⁰⁺
                      ( nonnegative-dist-ℝ _ _)
                        ( preserves-leq-mul-ℝ⁰⁺
                          ( nonnegative-ℝ⁺ (inv-ℝ⁺ (pos-type-[a,b] x)))
                          ( nonnegative-real-ℚ⁺ M⁺)
                          ( nonnegative-dist-ℝ _ _)
                          ( nonnegative-real-ℚ⁺ (M⁻³ *ℚ⁺ ε))
                          ( leq-le-ℝ (real-inv-type-[a,b]<M x))
                          ( leq-dist-neighborhood-ℝ _ _ _ Nδxy)))
              ≤ ( real-ℚ (square-ℚ M) *ℝ (real-ℚ M *ℝ real-ℚ⁺ (M⁻³ *ℚ⁺ ε))) *ℝ
                ( dist-ℝ (pr1 x) (pr1 y))
                by leq-eq-ℝ (inv (associative-mul-ℝ _ _ _))
              ≤ ( real-ℚ (square-ℚ M) *ℝ real-ℚ M *ℝ real-ℚ⁺ (M⁻³ *ℚ⁺ ε)) *ℝ
                ( dist-ℝ (pr1 x) (pr1 y))
                by leq-eq-ℝ (ap-mul-ℝ (inv (associative-mul-ℝ _ _ _)) refl)
              ≤ ( real-ℚ⁺ (power-ℚ⁺ 3 M⁺) *ℝ real-ℚ⁺ (M⁻³ *ℚ⁺ ε)) *ℝ
                ( dist-ℝ (pr1 x) (pr1 y))
                by leq-eq-ℝ (ap-mul-ℝ (ap-mul-ℝ (mul-real-ℚ _ _) refl) refl)
              ≤ ( real-ℚ⁺ (power-ℚ⁺ 3 M⁺ *ℚ⁺ (M⁻³ *ℚ⁺ ε))) *ℝ
                ( dist-ℝ (pr1 x) (pr1 y))
                by leq-eq-ℝ (ap-mul-ℝ (mul-real-ℚ _ _) refl)
              ≤ real-ℚ⁺ ε *ℝ dist-ℝ (pr1 x) (pr1 y)
                by
                  leq-eq-ℝ
                    ( ap-mul-ℝ (ap real-ℚ (is-section-left-div-ℚ⁺ _ _)) refl))
```
