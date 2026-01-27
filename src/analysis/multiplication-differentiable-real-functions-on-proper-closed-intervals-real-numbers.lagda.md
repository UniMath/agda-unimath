# Multiplication of differentiable real functions on proper closed intervals in the real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module analysis.multiplication-differentiable-real-functions-on-proper-closed-intervals-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import analysis.differentiable-real-functions-on-proper-closed-intervals-real-numbers

open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.minimum-positive-rational-numbers
open import elementary-number-theory.multiplication-positive-rational-numbers
open import elementary-number-theory.multiplicative-group-of-positive-rational-numbers
open import elementary-number-theory.nonzero-natural-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.existential-quantification
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
open import real-numbers.inequalities-addition-and-subtraction-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.multiplication-nonnegative-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.multiplication-uniformly-continuous-functions-proper-closed-intervals-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.proper-closed-intervals-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.strict-inequality-real-numbers
open import real-numbers.uniformly-continuous-functions-proper-closed-intervals-real-numbers
```

</details>

## Idea

The
{{#concept "product rule" Agda=derivative-mul-uniformly-continuous-map-proper-closed-interval-ℝ}}
for
[derivatives](analysis.derivatives-of-real-functions-on-proper-closed-intervals.md)
states that if `f` and `g` are
[uniformly continuous](real-numbers.uniformly-continuous-functions-proper-closed-intervals-real-numbers.md)
functions on a
[proper closed interval](real-numbers.proper-closed-intervals-real-numbers.md),
and they are both differentiable with uniformly continuous derivatives `f'` and
`g'`, then the product function `x ↦ f x * g x` is differentiable with
derivative `x ↦ f x * g' x + f' x * g x`.

## Proof

This proof is derived from Theorem 5 of Chapter 2 in
{{#cite BishopFoundations}}.

```agda
module _
  {l1 l2 l3 : Level}
  ([a,b] : proper-closed-interval-ℝ l1 l1)
  (f : uniformly-continuous-map-proper-closed-interval-ℝ l1 l2 [a,b])
  (g : uniformly-continuous-map-proper-closed-interval-ℝ l1 l3 [a,b])
  (f' :
    uniformly-continuous-map-proper-closed-interval-ℝ l1 (l1 ⊔ l2) [a,b])
  (g' :
    uniformly-continuous-map-proper-closed-interval-ℝ l1 (l1 ⊔ l3) [a,b])
  (is-derivative-f-f' :
    is-derivative-real-function-proper-closed-interval-ℝ
      ( [a,b])
      ( map-uniformly-continuous-map-proper-closed-interval-ℝ [a,b] f)
      ( map-uniformly-continuous-map-proper-closed-interval-ℝ [a,b] f'))
  (is-derivative-g-g' :
    is-derivative-real-function-proper-closed-interval-ℝ
      ( [a,b])
      ( map-uniformly-continuous-map-proper-closed-interval-ℝ [a,b] g)
      ( map-uniformly-continuous-map-proper-closed-interval-ℝ [a,b] g'))
  where

  map-derivative-mul-real-function-proper-closed-interval-ℝ :
    type-proper-closed-interval-ℝ l1 [a,b] → ℝ (l1 ⊔ l2 ⊔ l3)
  map-derivative-mul-real-function-proper-closed-interval-ℝ x =
    let
      map :
        {l4 : Level} →
        uniformly-continuous-map-proper-closed-interval-ℝ l1 l4 [a,b] →
        type-proper-closed-interval-ℝ l1 [a,b] → ℝ l4
      map = map-uniformly-continuous-map-proper-closed-interval-ℝ [a,b]
    in map f x *ℝ map g' x +ℝ map f' x *ℝ map g x

  abstract
    derivative-mul-uniformly-continuous-map-proper-closed-interval-ℝ :
      is-derivative-real-function-proper-closed-interval-ℝ
        ( [a,b])
        ( map-mul-uniformly-continuous-map-proper-closed-interval-ℝ
          ( [a,b])
          ( f)
          ( g))
        ( map-derivative-mul-real-function-proper-closed-interval-ℝ)
    derivative-mul-uniformly-continuous-map-proper-closed-interval-ℝ =
      let
        open
          do-syntax-trunc-Prop
            ( is-derivative-prop-real-function-proper-closed-interval-ℝ
              ( [a,b])
              ( map-mul-uniformly-continuous-map-proper-closed-interval-ℝ
                ( [a,b])
                ( f)
                ( g))
              ( map-derivative-mul-real-function-proper-closed-interval-ℝ))
        ((Mf , _) , is-bound-Mf) =
          nonnegative-upper-bound-abs-im-uniformly-continuous-map-proper-closed-interval-ℝ
            ( [a,b])
            ( f)
        ((Mg , _) , is-bound-Mg) =
          nonnegative-upper-bound-abs-im-uniformly-continuous-map-proper-closed-interval-ℝ
            ( [a,b])
            ( g)
        ((Mg' , _) , is-bound-Mg') =
          nonnegative-upper-bound-abs-im-uniformly-continuous-map-proper-closed-interval-ℝ
            ( [a,b])
            ( g')
        M₀ : ℝ (l1 ⊔ l2 ⊔ l3)
        M₀ = max-ℝ (max-ℝ Mf Mg) Mg'
        map-f =
          map-uniformly-continuous-map-proper-closed-interval-ℝ [a,b] f
        map-g =
          map-uniformly-continuous-map-proper-closed-interval-ℝ [a,b] g
        map-f' =
          map-uniformly-continuous-map-proper-closed-interval-ℝ [a,b] f'
        map-g' =
          map-uniformly-continuous-map-proper-closed-interval-ℝ [a,b] g'
        open inequality-reasoning-Large-Poset ℝ-Large-Poset
      in do
        (δf , is-mod-δf) ← is-derivative-f-f'
        (δg , is-mod-δg) ← is-derivative-g-g'
        (ωf , is-mod-ωf) ←
          is-ucont-map-uniformly-continuous-map-proper-closed-interval-ℝ
            ( [a,b])
            ( f)
        (M⁺ , M₀<M⁺) ← exists-greater-positive-rational-ℝ M₀
        let
          shrink ε = inv-ℚ⁺ (positive-rational-ℕ⁺ three-ℕ⁺ *ℚ⁺ M⁺) *ℚ⁺ ε
          δ ε =
            min-ℚ⁺ (min-ℚ⁺ (δf (shrink ε)) (δg (shrink ε))) (ωf (shrink ε))
        intro-exists
          ( δ)
          ( λ ε x@(xℝ , _) y@(yℝ , _) Nδxy →

            chain-of-inequalities
              dist-ℝ
                ( (map-f y *ℝ map-g y) -ℝ (map-f x *ℝ map-g x))
                ( (map-f x *ℝ map-g' x +ℝ map-f' x *ℝ map-g x) *ℝ (yℝ -ℝ xℝ))
              ≤ dist-ℝ
                  ( ( map-f y *ℝ map-g y) -ℝ (map-f x *ℝ map-g x))
                  ( ( (map-f x *ℝ map-g' x) *ℝ (yℝ -ℝ xℝ)) +ℝ
                    ( (map-f' x *ℝ map-g x) *ℝ (yℝ -ℝ xℝ)))
                by
                  leq-eq-ℝ (ap-dist-ℝ refl (right-distributive-mul-add-ℝ _ _ _))
              ≤ dist-ℝ
                  ( ( map-f y *ℝ map-g y) -ℝ (map-f x *ℝ map-g x))
                  ( ( (map-f x *ℝ map-g' x) *ℝ (yℝ -ℝ xℝ)) +ℝ
                    ( (map-f' x *ℝ (yℝ -ℝ xℝ)) *ℝ map-g x))
                by
                  leq-eq-ℝ
                    ( ap-dist-ℝ refl (ap-add-ℝ refl (right-swap-mul-ℝ _ _ _)))
              ≤ abs-ℝ
                  ( ( ( map-f y *ℝ map-g y) -ℝ
                      ( (map-f x *ℝ map-g' x) *ℝ (yℝ -ℝ xℝ))) +ℝ
                    ( ( neg-ℝ (map-f x *ℝ map-g x)) -ℝ
                      ( map-f' x *ℝ (yℝ -ℝ xℝ)) *ℝ map-g x))
                by leq-eq-ℝ (ap abs-ℝ (interchange-law-diff-add-ℝ _ _ _ _))
              ≤ dist-ℝ
                  ( ( map-f y *ℝ map-g y) -ℝ
                    ( (map-f x *ℝ map-g' x) *ℝ (yℝ -ℝ xℝ)))
                  ( ( map-f x *ℝ map-g x) +ℝ
                    ( map-f' x *ℝ (yℝ -ℝ xℝ)) *ℝ map-g x)
                by
                  leq-eq-ℝ
                    ( inv
                      ( ap abs-ℝ (ap-add-ℝ refl (distributive-neg-add-ℝ _ _))))
              ≤ dist-ℝ
                  ( ( map-f y *ℝ map-g y) -ℝ
                    ( (map-f x *ℝ map-g' x) *ℝ (yℝ -ℝ xℝ)))
                  ( ( map-f x +ℝ map-f' x *ℝ (yℝ -ℝ xℝ)) *ℝ map-g x)
                by
                  leq-eq-ℝ
                    ( ap-dist-ℝ refl (inv (right-distributive-mul-add-ℝ _ _ _)))
              ≤ dist-ℝ
                  ( ( ( map-f y *ℝ map-g y) -ℝ
                      ( (map-f x *ℝ map-g' x) *ℝ (yℝ -ℝ xℝ))) -ℝ
                    ( map-f y *ℝ map-g x))
                  ( ( ( map-f x +ℝ map-f' x *ℝ (yℝ -ℝ xℝ)) *ℝ map-g x) -ℝ
                    ( map-f y *ℝ map-g x))
                by
                  leq-sim-ℝ'
                    ( preserves-dist-right-add-ℝ
                      ( neg-ℝ (map-f y *ℝ map-g x))
                      ( _)
                      ( _))
              ≤ abs-ℝ
                  ( ( ( ( map-f y *ℝ map-g y) -ℝ
                        ( (map-f x *ℝ map-g' x) *ℝ (yℝ -ℝ xℝ))) -ℝ
                      ( map-f y *ℝ map-g x)) +ℝ
                    ( ( map-f y *ℝ map-g x) -ℝ
                      ( (map-f x +ℝ map-f' x *ℝ (yℝ -ℝ xℝ)) *ℝ map-g x)))
                by
                  leq-eq-ℝ
                    ( ap abs-ℝ (ap-add-ℝ refl (distributive-neg-diff-ℝ _ _)))
              ≤ ( dist-ℝ
                  ( ( map-f y *ℝ map-g y) -ℝ
                    ( (map-f x *ℝ map-g' x) *ℝ (yℝ -ℝ xℝ)))
                  ( map-f y *ℝ map-g x)) +ℝ
                ( dist-ℝ
                  ( map-f y *ℝ map-g x)
                  ( (map-f x +ℝ map-f' x *ℝ (yℝ -ℝ xℝ)) *ℝ map-g x))
                by triangle-inequality-abs-ℝ _ _
              ≤ ( dist-ℝ
                  ( (map-f y *ℝ map-g y) -ℝ (map-f y *ℝ map-g x))
                  ( (map-f x *ℝ map-g' x) *ℝ (yℝ -ℝ xℝ))) +ℝ
                ( ( dist-ℝ (map-f y) (map-f x +ℝ map-f' x *ℝ (yℝ -ℝ xℝ))) *ℝ
                  ( abs-ℝ (map-g x)))
                by
                  leq-eq-ℝ
                    ( ap-add-ℝ
                      ( ap abs-ℝ (right-swap-add-ℝ _ _ _))
                      ( inv (right-distributive-abs-mul-dist-ℝ _ _ _)))
              ≤ ( dist-ℝ
                  ( map-f y *ℝ (map-g y -ℝ map-g x))
                  ( (map-f x *ℝ map-g' x) *ℝ (yℝ -ℝ xℝ))) +ℝ
                ( ( abs-ℝ
                    ( ( map-f y) +ℝ
                      ( neg-ℝ (map-f x) -ℝ map-f' x *ℝ (yℝ -ℝ xℝ)))) *ℝ
                  ( abs-ℝ (map-g x)))
                by
                  leq-eq-ℝ
                    ( ap-add-ℝ
                      ( ap-dist-ℝ
                        ( inv (left-distributive-mul-diff-ℝ _ _ _))
                        ( refl))
                      ( ap-mul-ℝ
                        ( ap abs-ℝ (ap-add-ℝ refl (distributive-neg-add-ℝ _ _)))
                        ( refl)))
              ≤ ( dist-ℝ
                  ( ( map-f y *ℝ (map-g y -ℝ map-g x)) -ℝ
                    ( map-f y *ℝ (map-g' x *ℝ (yℝ -ℝ xℝ))))
                  ( ( (map-f x *ℝ map-g' x) *ℝ (yℝ -ℝ xℝ)) -ℝ
                    ( map-f y *ℝ (map-g' x *ℝ (yℝ -ℝ xℝ))))) +ℝ
                ( ( dist-ℝ (map-f y -ℝ map-f x) (map-f' x *ℝ (yℝ -ℝ xℝ))) *ℝ
                  ( abs-ℝ (map-g x)))
                by
                  preserves-leq-add-ℝ
                    ( leq-sim-ℝ' (preserves-dist-right-add-ℝ _ _ _))
                    ( leq-eq-ℝ
                      ( ap-mul-ℝ
                        ( ap abs-ℝ (inv (associative-add-ℝ _ _ _)))
                        ( refl)))
              ≤ ( dist-ℝ
                  ( ( ( map-f y) *ℝ
                      ( (map-g y -ℝ map-g x) -ℝ map-g' x *ℝ (yℝ -ℝ xℝ))))
                  ( ( map-f x *ℝ (map-g' x *ℝ (yℝ -ℝ xℝ))) -ℝ
                    ( map-f y *ℝ (map-g' x *ℝ (yℝ -ℝ xℝ))))) +ℝ
                ( real-ℚ⁺ (shrink ε) *ℝ dist-ℝ xℝ yℝ *ℝ real-ℚ⁺ M⁺)
                by
                  preserves-leq-add-ℝ
                    ( leq-eq-ℝ
                      ( ap-dist-ℝ
                        ( inv (left-distributive-mul-diff-ℝ _ _ _))
                        ( ap-diff-ℝ (associative-mul-ℝ _ _ _) refl)))
                    ( preserves-leq-mul-ℝ⁰⁺
                      ( nonnegative-dist-ℝ _ _)
                      ( ( nonnegative-real-ℚ⁺ (shrink ε)) *ℝ⁰⁺
                        ( nonnegative-dist-ℝ xℝ yℝ))
                      ( nonnegative-abs-ℝ _)
                      ( nonnegative-real-ℚ⁺ M⁺)
                      ( is-mod-δf
                        ( shrink ε)
                        ( x)
                        ( y)
                        ( weakly-monotonic-neighborhood-ℝ
                          ( xℝ)
                          ( yℝ)
                          ( δ ε)
                          ( δf (shrink ε))
                          ( transitive-leq-ℚ _ _ _
                            ( leq-left-min-ℚ⁺
                              ( δf (shrink ε))
                              ( δg (shrink ε)))
                            ( leq-left-min-ℚ⁺ _ _))
                          ( Nδxy)))
                      ( chain-of-inequalities
                        abs-ℝ (map-g x)
                        ≤ Mg
                          by is-bound-Mg x
                        ≤ M₀
                          by
                            transitive-leq-ℝ _ _ _
                              ( leq-left-max-ℝ _ _)
                              ( leq-right-max-ℝ _ _)
                        ≤ real-ℚ⁺ M⁺
                          by leq-le-ℝ M₀<M⁺))
              ≤ ( abs-ℝ
                  ( ( ( map-f y) *ℝ
                      ( (map-g y -ℝ map-g x) -ℝ map-g' x *ℝ (yℝ -ℝ xℝ))) +ℝ
                    ( ( map-f y *ℝ (map-g' x *ℝ (yℝ -ℝ xℝ))) -ℝ
                      ( map-f x *ℝ (map-g' x *ℝ (yℝ -ℝ xℝ)))))) +ℝ
                ( real-ℚ⁺ (shrink ε) *ℝ dist-ℝ xℝ yℝ *ℝ real-ℚ⁺ M⁺)
                by
                  leq-eq-ℝ
                    ( ap-add-ℝ
                      ( ap abs-ℝ (ap-add-ℝ refl (distributive-neg-diff-ℝ _ _)))
                      ( refl))
              ≤ ( abs-ℝ
                  ( ( map-f y) *ℝ
                    ( (map-g y -ℝ map-g x) -ℝ map-g' x *ℝ (yℝ -ℝ xℝ)))) +ℝ
                ( dist-ℝ
                  ( map-f y *ℝ (map-g' x *ℝ (yℝ -ℝ xℝ)))
                  ( map-f x *ℝ (map-g' x *ℝ (yℝ -ℝ xℝ)))) +ℝ
                ( real-ℚ⁺ (shrink ε) *ℝ dist-ℝ xℝ yℝ *ℝ real-ℚ⁺ M⁺)
                by
                  preserves-leq-right-add-ℝ _ _ _
                    ( triangle-inequality-abs-ℝ _ _)
              ≤ ( ( abs-ℝ (map-f y)) *ℝ
                  ( dist-ℝ (map-g y -ℝ map-g x) (map-g' x *ℝ (yℝ -ℝ xℝ)))) +ℝ
                ( ( dist-ℝ (map-f y) (map-f x)) *ℝ
                  ( abs-ℝ (map-g' x *ℝ (yℝ -ℝ xℝ)))) +ℝ
                ( real-ℚ⁺ (shrink ε) *ℝ dist-ℝ xℝ yℝ *ℝ real-ℚ⁺ M⁺)
                by
                  leq-eq-ℝ
                    ( ap-add-ℝ
                      ( ap-add-ℝ
                        ( abs-mul-ℝ _ _)
                        ( inv (right-distributive-abs-mul-dist-ℝ _ _ _)))
                      ( refl))
              ≤ ( ( abs-ℝ (map-f y)) *ℝ
                  ( dist-ℝ (map-g y -ℝ map-g x) (map-g' x *ℝ (yℝ -ℝ xℝ)))) +ℝ
                ( ( dist-ℝ (map-f y) (map-f x)) *ℝ
                  ( abs-ℝ (map-g' x) *ℝ dist-ℝ xℝ yℝ)) +ℝ
                ( real-ℚ⁺ (shrink ε) *ℝ real-ℚ⁺ M⁺ *ℝ dist-ℝ xℝ yℝ)
                by
                  leq-eq-ℝ
                    ( ap-add-ℝ
                      ( ap-add-ℝ
                        ( refl)
                        ( ap-mul-ℝ
                          ( refl)
                          ( ( abs-mul-ℝ _ _) ∙
                            ( ap-mul-ℝ refl (commutative-dist-ℝ _ _)))))
                      ( right-swap-mul-ℝ _ _ _))
              ≤ ( real-ℚ⁺ M⁺ *ℝ (real-ℚ⁺ (shrink ε) *ℝ dist-ℝ xℝ yℝ)) +ℝ
                ( real-ℚ⁺ (shrink ε) *ℝ (real-ℚ⁺ M⁺ *ℝ dist-ℝ xℝ yℝ)) +ℝ
                ( real-ℚ⁺ (shrink ε) *ℝ real-ℚ⁺ M⁺ *ℝ dist-ℝ xℝ yℝ)
                by
                  preserves-leq-right-add-ℝ _ _ _
                    ( preserves-leq-add-ℝ
                      ( preserves-leq-mul-ℝ⁰⁺
                        ( nonnegative-abs-ℝ _)
                        ( nonnegative-real-ℚ⁺ M⁺)
                        ( nonnegative-dist-ℝ _ _)
                        ( ( nonnegative-real-ℚ⁺ (shrink ε)) *ℝ⁰⁺
                          ( nonnegative-dist-ℝ xℝ yℝ))
                        ( chain-of-inequalities
                          abs-ℝ (map-f y)
                          ≤ Mf
                            by is-bound-Mf y
                          ≤ max-ℝ Mf Mg
                            by leq-left-max-ℝ _ _
                          ≤ M₀
                            by leq-left-max-ℝ _ _
                          ≤ real-ℚ⁺ M⁺
                            by leq-le-ℝ M₀<M⁺)
                        ( is-mod-δg
                          ( shrink ε)
                          ( x)
                          ( y)
                          ( weakly-monotonic-neighborhood-ℝ
                            ( xℝ)
                            ( yℝ)
                            ( δ ε)
                            ( δg (shrink ε))
                            ( transitive-leq-ℚ _ _ _
                              ( leq-right-min-ℚ⁺
                                ( δf (shrink ε))
                                ( δg (shrink ε)))
                              ( leq-left-min-ℚ⁺ _ _))
                            ( Nδxy))))
                      ( preserves-leq-mul-ℝ⁰⁺
                        ( nonnegative-dist-ℝ _ _)
                        ( nonnegative-real-ℚ⁺ (shrink ε))
                        ( nonnegative-abs-ℝ _ *ℝ⁰⁺ nonnegative-dist-ℝ _ _)
                        ( nonnegative-real-ℚ⁺ M⁺ *ℝ⁰⁺ nonnegative-dist-ℝ _ _)
                        ( leq-dist-neighborhood-ℝ
                          ( shrink ε)
                          ( map-f y)
                          ( map-f x)
                          ( is-mod-ωf
                            ( y)
                            ( shrink ε)
                            ( x)
                            ( weakly-monotonic-neighborhood-ℝ
                              ( yℝ)
                              ( xℝ)
                              ( δ ε)
                              ( ωf (shrink ε))
                              ( leq-right-min-ℚ⁺ _ _)
                              ( is-symmetric-neighborhood-ℝ (δ ε) xℝ yℝ Nδxy))))
                        ( preserves-leq-right-mul-ℝ⁰⁺
                          ( nonnegative-dist-ℝ _ _)
                          ( chain-of-inequalities
                            abs-ℝ (map-g' x)
                            ≤ Mg'
                              by is-bound-Mg' x
                            ≤ M₀
                              by leq-right-max-ℝ _ _
                            ≤ real-ℚ⁺ M⁺
                              by leq-le-ℝ M₀<M⁺))))
              ≤ ( real-ℚ⁺ (shrink ε) *ℝ (real-ℚ⁺ M⁺ *ℝ dist-ℝ xℝ yℝ)) +ℝ
                ( real-ℚ⁺ (shrink ε) *ℝ (real-ℚ⁺ M⁺ *ℝ dist-ℝ xℝ yℝ)) +ℝ
                ( real-ℚ⁺ (shrink ε) *ℝ (real-ℚ⁺ M⁺ *ℝ dist-ℝ xℝ yℝ))
                by
                  leq-eq-ℝ
                    ( ap-add-ℝ
                      ( ap-add-ℝ (left-swap-mul-ℝ _ _ _) refl)
                      ( associative-mul-ℝ _ _ _))
              ≤ ( real-ℕ 3) *ℝ
                ( ( real-ℚ⁺
                    ( inv-ℚ⁺ (positive-rational-ℕ⁺ three-ℕ⁺ *ℚ⁺ M⁺) *ℚ⁺ ε)) *ℝ
                  ( real-ℚ⁺ M⁺ *ℝ dist-ℝ xℝ yℝ))
                by leq-eq-ℝ (inv (left-mul-real-ℕ 3 _))
              ≤ ( real-ℕ 3) *ℝ
                ( ( real-ℚ⁺
                    ( inv-ℚ⁺ (positive-rational-ℕ⁺ three-ℕ⁺ *ℚ⁺ M⁺) *ℚ⁺ ε)) *ℝ
                  ( real-ℚ⁺ M⁺) *ℝ
                  ( dist-ℝ xℝ yℝ))
                by leq-eq-ℝ (ap-mul-ℝ refl (inv (associative-mul-ℝ _ _ _)))
              ≤ ( real-ℕ 3) *ℝ
                ( ( real-ℚ⁺
                    ( ( inv-ℚ⁺ (positive-rational-ℕ⁺ three-ℕ⁺ *ℚ⁺ M⁺) *ℚ⁺ ε) *ℚ⁺
                      ( M⁺))) *ℝ
                  ( dist-ℝ xℝ yℝ))
                by leq-eq-ℝ (ap-mul-ℝ refl (ap-mul-ℝ (mul-real-ℚ _ _) refl))
              ≤ ( real-ℕ 3) *ℝ
                ( ( real-ℚ⁺
                    ( ( inv-ℚ⁺ (positive-rational-ℕ⁺ three-ℕ⁺ *ℚ⁺ M⁺)) *ℚ⁺
                      ( M⁺) *ℚ⁺
                      ( ε))) *ℝ
                  ( dist-ℝ xℝ yℝ))
                by
                  leq-eq-ℝ
                    ( ap-mul-ℝ
                      ( refl)
                      ( ap-mul-ℝ (ap real-ℚ⁺ (right-swap-mul-ℚ⁺ _ _ _)) refl))
              ≤ ( real-ℕ 3) *ℝ
                ( ( real-ℚ⁺
                    ( ( inv-ℚ⁺ (positive-rational-ℕ⁺ three-ℕ⁺)) *ℚ⁺
                      ( inv-ℚ⁺ M⁺) *ℚ⁺
                      ( M⁺) *ℚ⁺
                      ( ε))) *ℝ
                  ( dist-ℝ xℝ yℝ))
                by
                  leq-eq-ℝ
                    ( ap-mul-ℝ
                      ( refl)
                      ( ap-mul-ℝ
                        ( ap real-ℚ⁺
                          ( ap-mul-ℚ⁺
                            ( ap-mul-ℚ⁺ (distributive-inv-mul-ℚ⁺ _ _) refl)
                            ( refl)))
                        ( refl)))
              ≤ ( real-ℕ 3) *ℝ
                ( ( real-ℚ⁺ (inv-ℚ⁺ (positive-rational-ℕ⁺ three-ℕ⁺) *ℚ⁺ ε)) *ℝ
                  ( dist-ℝ xℝ yℝ))
                by
                  leq-eq-ℝ
                    ( ap-mul-ℝ
                      ( refl)
                      ( ap-mul-ℝ
                        ( ap real-ℚ⁺
                          ( ap-mul-ℚ⁺
                            ( eq-ℚ⁺ (is-section-right-div-ℚ⁺ M⁺ _))
                            ( refl)))
                        ( refl)))
              ≤ ( ( real-ℕ 3) *ℝ
                  ( real-ℚ⁺ (inv-ℚ⁺ (positive-rational-ℕ⁺ three-ℕ⁺) *ℚ⁺ ε))) *ℝ
                ( dist-ℝ xℝ yℝ)
                by leq-eq-ℝ (inv (associative-mul-ℝ _ _ _))
              ≤ ( real-ℚ⁺
                  ( ( positive-rational-ℕ⁺ three-ℕ⁺) *ℚ⁺
                    ( inv-ℚ⁺ (positive-rational-ℕ⁺ three-ℕ⁺) *ℚ⁺ ε))) *ℝ
                ( dist-ℝ xℝ yℝ)
                by leq-eq-ℝ (ap-mul-ℝ (mul-real-ℚ _ _) refl)
              ≤ real-ℚ⁺ ε *ℝ dist-ℝ xℝ yℝ
                by
                  leq-eq-ℝ
                    ( ap-mul-ℝ
                      ( ap real-ℚ⁺ (eq-ℚ⁺ (is-section-left-div-ℚ⁺ _ _)))
                      ( refl)))

module _
  {l1 l2 l3 : Level}
  ([a,b] : proper-closed-interval-ℝ l1 l1)
  (f : differentiable-real-function-proper-closed-interval-ℝ l2 [a,b])
  (g : differentiable-real-function-proper-closed-interval-ℝ l3 [a,b])
  where

  map-mul-differentiable-real-function-proper-closed-interval-ℝ :
    type-proper-closed-interval-ℝ l1 [a,b] → ℝ (l2 ⊔ l3)
  map-mul-differentiable-real-function-proper-closed-interval-ℝ x =
    ( map-differentiable-real-function-proper-closed-interval-ℝ [a,b] f x) *ℝ
    ( map-differentiable-real-function-proper-closed-interval-ℝ [a,b] g x)

  abstract
    is-differentiable-map-mul-differentiable-real-function-proper-closed-interval-ℝ :
      is-differentiable-real-function-proper-closed-interval-ℝ
        ( [a,b])
        ( map-mul-differentiable-real-function-proper-closed-interval-ℝ)
    is-differentiable-map-mul-differentiable-real-function-proper-closed-interval-ℝ =
      let
        (map-f , map-f' , Df=f') = f
        (map-g , map-g' , Dg=g') = g
      in
        ( ( λ x → map-f x *ℝ map-g' x +ℝ map-f' x *ℝ map-g x) ,
          derivative-mul-uniformly-continuous-map-proper-closed-interval-ℝ
            ( [a,b])
            ( ucont-map-differentiable-real-function-proper-closed-interval-ℝ
              ( [a,b])
              ( f))
            ( ucont-map-differentiable-real-function-proper-closed-interval-ℝ
              ( [a,b])
              ( g))
            ( ucont-derivative-differentiable-real-function-proper-closed-interval-ℝ
              ( [a,b])
              ( f))
            ( ucont-derivative-differentiable-real-function-proper-closed-interval-ℝ
              ( [a,b])
              ( g))
            ( Df=f')
            ( Dg=g'))
```

## External links

- [Product rule](https://en.wikipedia.org/wiki/Product_rule) on Wikipedia
