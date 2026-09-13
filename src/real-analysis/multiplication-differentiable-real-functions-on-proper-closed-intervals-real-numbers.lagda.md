# Multiplication of differentiable real functions on proper closed intervals in the real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-analysis.multiplication-differentiable-real-functions-on-proper-closed-intervals-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-positive-rational-numbers
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

open import real-analysis.differentiable-real-maps-on-proper-closed-intervals-real-numbers

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
open import real-numbers.multiplication-uniformly-continuous-real-maps-proper-closed-intervals-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.proper-closed-intervals-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-real-numbers
open import real-numbers.strict-inequality-real-numbers
open import real-numbers.uniformly-continuous-real-maps-proper-closed-intervals-real-numbers
```

</details>

## Idea

The
{{#concept "product rule" Agda=is-derivative-mul-uniformly-continuous-real-map-proper-closed-interval-ℝ}}
for
[derivatives](real-analysis.differentiable-real-maps-on-proper-closed-intervals-real-numbers.md)
states that if `f` and `g` are
[uniformly continuous](real-numbers.uniformly-continuous-real-maps-proper-closed-intervals-real-numbers.md)
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
  (f@(map-f , _) :
      uniformly-continuous-real-map-proper-closed-interval-ℝ l1 l2 [a,b])
  (g@(map-g , _) :
      uniformly-continuous-real-map-proper-closed-interval-ℝ l1 l3 [a,b])
  (f'@(map-f' , _) :
    uniformly-continuous-real-map-proper-closed-interval-ℝ l1 (l1 ⊔ l2) [a,b])
  (g'@(map-g' , _) :
    uniformly-continuous-real-map-proper-closed-interval-ℝ l1 (l1 ⊔ l3) [a,b])
  (is-derivative-f-f' :
    is-derivative-real-map-proper-closed-interval-ℝ
      ( [a,b])
      ( map-uniformly-continuous-real-map-proper-closed-interval-ℝ [a,b] f)
      ( map-uniformly-continuous-real-map-proper-closed-interval-ℝ [a,b] f'))
  (is-derivative-g-g' :
    is-derivative-real-map-proper-closed-interval-ℝ
      ( [a,b])
      ( map-uniformly-continuous-real-map-proper-closed-interval-ℝ [a,b] g)
      ( map-uniformly-continuous-real-map-proper-closed-interval-ℝ [a,b] g'))
  where

  map-derivative-mul-real-map-proper-closed-interval-ℝ :
    type-proper-closed-interval-ℝ l1 [a,b] → ℝ (l1 ⊔ l2 ⊔ l3)
  map-derivative-mul-real-map-proper-closed-interval-ℝ x =
    let
      map :
        {l4 : Level} →
        uniformly-continuous-real-map-proper-closed-interval-ℝ l1 l4 [a,b] →
        type-proper-closed-interval-ℝ l1 [a,b] → ℝ l4
      map = map-uniformly-continuous-real-map-proper-closed-interval-ℝ [a,b]
    in map f x *ℝ map g' x +ℝ map f' x *ℝ map g x

  abstract
    lemma-is-derivative-mul-uniformly-continuous-real-map-proper-closed-interval-ℝ :
      (x y : type-proper-closed-interval-ℝ l1 [a,b]) (z : ℝ l1) →
      dist-ℝ
        ( (map-f y *ℝ map-g y) -ℝ (map-f x *ℝ map-g x))
        ( (map-f x *ℝ map-g' x +ℝ map-f' x *ℝ map-g x) *ℝ z) ＝
      abs-ℝ
        ( ( map-f y *ℝ (map-g y -ℝ map-g x) -ℝ map-f x *ℝ (map-g' x *ℝ z)) +ℝ
          ( (map-f y -ℝ map-f x -ℝ map-f' x *ℝ z)) *ℝ map-g x)
    lemma-is-derivative-mul-uniformly-continuous-real-map-proper-closed-interval-ℝ
      x y z =
      let
        fy = map-f y
        gy = map-g y
        fx = map-f x
        gx = map-g x
        f'x = map-f' x
        g'x = map-g' x
      in
        equational-reasoning
          dist-ℝ (fy *ℝ gy -ℝ fx *ℝ gx) ((fx *ℝ g'x +ℝ f'x *ℝ gx) *ℝ z)
          ＝ dist-ℝ (fy *ℝ gy -ℝ fx *ℝ gx) (fx *ℝ g'x *ℝ z +ℝ f'x *ℝ gx *ℝ z)
            by ap-dist-ℝ refl (right-distributive-mul-add-ℝ _ _ z)
          ＝ dist-ℝ (fy *ℝ gy -ℝ fx *ℝ gx) (fx *ℝ g'x *ℝ z +ℝ f'x *ℝ z *ℝ gx)
            by ap-dist-ℝ refl (ap-add-ℝ refl (right-swap-mul-ℝ f'x gx z))
          ＝
            abs-ℝ
              ( ( fy *ℝ gy -ℝ fx *ℝ g'x *ℝ z) +ℝ
                ( neg-ℝ (fx *ℝ gx) -ℝ f'x *ℝ z *ℝ gx))
            by ap abs-ℝ (interchange-law-diff-add-ℝ _ _ _ _)
          ＝ dist-ℝ (fy *ℝ gy -ℝ fx *ℝ g'x *ℝ z) (fx *ℝ gx +ℝ f'x *ℝ z *ℝ gx)
            by ap abs-ℝ (ap-add-ℝ refl (inv (distributive-neg-add-ℝ _ _)))
          ＝ dist-ℝ (fy *ℝ gy -ℝ fx *ℝ g'x *ℝ z) ((fx +ℝ f'x *ℝ z) *ℝ gx)
            by
              ap-dist-ℝ
                { l1 ⊔ l2 ⊔ l3} -- the compiler seems to need a little help
                ( refl)
                ( inv (right-distributive-mul-add-ℝ _ _ _))
          ＝
            dist-ℝ
              ( (fy *ℝ gy -ℝ fx *ℝ g'x *ℝ z) -ℝ fy *ℝ gx)
              ( (fx +ℝ f'x *ℝ z) *ℝ gx -ℝ fy *ℝ gx)
            by inv (eq-sim-ℝ (preserves-dist-right-add-ℝ _ _ _))
          ＝
            dist-ℝ
              ( (fy *ℝ gy -ℝ fy *ℝ gx) -ℝ fx *ℝ g'x *ℝ z)
              ( ((fx +ℝ f'x *ℝ z) -ℝ fy) *ℝ gx)
            by
              ap-dist-ℝ
                { l1 ⊔ l2 ⊔ l3}
                ( right-swap-add-ℝ (fy *ℝ gy) _ (neg-ℝ (fy *ℝ gx)))
                ( inv (right-distributive-mul-diff-ℝ _ _ _))
          ＝
            dist-ℝ
              ( fy *ℝ (gy -ℝ gx) -ℝ fx *ℝ g'x *ℝ z)
              ( ((fx +ℝ f'x *ℝ z) -ℝ fy) *ℝ gx)
            by
              ap-dist-ℝ
                { l1 ⊔ l2 ⊔ l3}
                ( ap
                  ( _-ℝ fx *ℝ g'x *ℝ z)
                  ( inv (left-distributive-mul-diff-ℝ _ _ _)))
                ( refl)
          ＝
            abs-ℝ
              ( ( fy *ℝ (gy -ℝ gx) -ℝ fx *ℝ g'x *ℝ z) +ℝ
                ( neg-ℝ ((fx +ℝ f'x *ℝ z) -ℝ fy) *ℝ gx))
            by ap abs-ℝ (ap-add-ℝ refl (inv (left-negative-law-mul-ℝ _ _)))
          ＝
            abs-ℝ
              ( ( fy *ℝ (gy -ℝ gx) -ℝ fx *ℝ g'x *ℝ z) +ℝ
                ( fy -ℝ (fx +ℝ f'x *ℝ z)) *ℝ gx)
            by
              ap
                ( abs-ℝ)
                ( ap-add-ℝ refl (ap-mul-ℝ (distributive-neg-diff-ℝ _ _) refl))
          ＝
            abs-ℝ
              ( ( fy *ℝ (gy -ℝ gx) -ℝ fx *ℝ (g'x *ℝ z)) +ℝ
                ( (fy -ℝ fx -ℝ f'x *ℝ z)) *ℝ gx)
            by
              ap
                ( abs-ℝ)
                ( ap-add-ℝ
                  ( ap-diff-ℝ refl (associative-mul-ℝ fx g'x z))
                  ( ap-mul-ℝ (inv (associative-diff-ℝ _ _ _)) refl))

  abstract
    is-derivative-mul-uniformly-continuous-real-map-proper-closed-interval-ℝ :
      is-derivative-real-map-proper-closed-interval-ℝ
        ( [a,b])
        ( map-mul-uniformly-continuous-real-map-proper-closed-interval-ℝ
          ( [a,b])
          ( f)
          ( g))
        ( map-derivative-mul-real-map-proper-closed-interval-ℝ)
    is-derivative-mul-uniformly-continuous-real-map-proper-closed-interval-ℝ =
      let
        open
          do-syntax-trunc-Prop
            ( is-derivative-prop-real-map-proper-closed-interval-ℝ
              ( [a,b])
              ( map-mul-uniformly-continuous-real-map-proper-closed-interval-ℝ
                ( [a,b])
                ( f)
                ( g))
              ( map-derivative-mul-real-map-proper-closed-interval-ℝ))
        ((Mf , _) , is-bound-Mf) =
          nonnegative-upper-bound-abs-im-uniformly-continuous-real-map-proper-closed-interval-ℝ
            ( [a,b])
            ( f)
        ((Mg , _) , is-bound-Mg) =
          nonnegative-upper-bound-abs-im-uniformly-continuous-real-map-proper-closed-interval-ℝ
            ( [a,b])
            ( g)
        ((Mg' , _) , is-bound-Mg') =
          nonnegative-upper-bound-abs-im-uniformly-continuous-real-map-proper-closed-interval-ℝ
            ( [a,b])
            ( g')
        M₀ = max-ℝ (max-ℝ Mf Mg) Mg'
        open inequality-reasoning-Large-Poset ℝ-Large-Poset
      in do
        (δf , is-mod-δf) ← is-derivative-f-f'
        (δg , is-mod-δg) ← is-derivative-g-g'
        (ωf , is-mod-ωf) ←
          is-uniformly-continuous-map-uniformly-continuous-real-map-proper-closed-interval-ℝ
            ( [a,b])
            ( f)
        (M⁺ , M₀<M⁺) ← exists-greater-positive-rational-ℝ M₀
        let
          shrink ε = inv-ℚ⁺ (three-ℚ⁺ *ℚ⁺ M⁺) *ℚ⁺ ε
          δ ε = min-ℚ⁺ (min-ℚ⁺ (δf (shrink ε)) (δg (shrink ε))) (ωf (shrink ε))
          |g|≤M⁺ x =
            chain-of-inequalities
              abs-ℝ (map-g x)
              ≤ Mg
                by is-bound-Mg x
              ≤ M₀
                by
                  transitive-leq-ℝ _ _ _
                    ( leq-left-max-ℝ _ _)
                    ( leq-right-max-ℝ _ _)
              ≤ real-ℚ⁺ M⁺
                by leq-le-ℝ M₀<M⁺
          |f|≤M⁺ x =
            chain-of-inequalities
              abs-ℝ (map-f x)
              ≤ Mf
                by is-bound-Mf x
              ≤ M₀
                by
                  transitive-leq-ℝ _ _ _
                    ( leq-left-max-ℝ _ _)
                    ( leq-left-max-ℝ _ _)
              ≤ real-ℚ⁺ M⁺
                by leq-le-ℝ M₀<M⁺
          |g'|≤M⁺ x =
            chain-of-inequalities
              abs-ℝ (map-g' x)
              ≤ Mg'
                by is-bound-Mg' x
              ≤ M₀
                by leq-right-max-ℝ _ _
              ≤ real-ℚ⁺ M⁺
                by leq-le-ℝ M₀<M⁺
          δ≤δf-shrink ε =
            transitive-leq-ℚ⁺
              ( δ ε)
              ( min-ℚ⁺ (δf (shrink ε)) (δg (shrink ε)))
              ( δf (shrink ε))
              ( leq-left-min-ℚ⁺ (δf (shrink ε)) (δg (shrink ε)))
              ( leq-left-min-ℚ⁺ _ _)
          δ≤δg-shrink ε =
            transitive-leq-ℚ⁺
              ( δ ε)
              ( min-ℚ⁺ (δf (shrink ε)) (δg (shrink ε)))
              ( δg (shrink ε))
              ( leq-right-min-ℚ⁺ (δf (shrink ε)) (δg (shrink ε)))
              ( leq-left-min-ℚ⁺ _ _)
        intro-exists
          ( δ)
          ( λ ε x@(xℝ , _) y@(yℝ , _) Nδxy →
            chain-of-inequalities
              dist-ℝ
                ( (map-f y *ℝ map-g y) -ℝ (map-f x *ℝ map-g x))
                ( (map-f x *ℝ map-g' x +ℝ map-f' x *ℝ map-g x) *ℝ (yℝ -ℝ xℝ))
              ≤ abs-ℝ
                  ( ( ( map-f y *ℝ (map-g y -ℝ map-g x)) -ℝ
                      ( map-f x *ℝ (map-g' x *ℝ (yℝ -ℝ xℝ)))) +ℝ
                    ( ( map-f y -ℝ map-f x -ℝ map-f' x *ℝ (yℝ -ℝ xℝ))) *ℝ
                      ( map-g x))
                by
                  leq-eq-ℝ
                    ( lemma-is-derivative-mul-uniformly-continuous-real-map-proper-closed-interval-ℝ
                      ( x)
                      ( y)
                      ( yℝ -ℝ xℝ))
              ≤ ( dist-ℝ
                  ( map-f y *ℝ (map-g y -ℝ map-g x))
                  ( map-f x *ℝ (map-g' x *ℝ (yℝ -ℝ xℝ)))) +ℝ
                ( abs-ℝ
                  ( (map-f y -ℝ map-f x -ℝ map-f' x *ℝ (yℝ -ℝ xℝ)) *ℝ map-g x))
                by triangle-inequality-abs-ℝ _ _
              ≤ ( dist-ℝ
                  ( map-f y *ℝ (map-g y -ℝ map-g x))
                  ( map-f y *ℝ (map-g' x *ℝ (yℝ -ℝ xℝ)))) +ℝ
                ( dist-ℝ
                  ( map-f y *ℝ (map-g' x *ℝ (yℝ -ℝ xℝ)))
                  ( map-f x *ℝ (map-g' x *ℝ (yℝ -ℝ xℝ)))) +ℝ
                ( ( dist-ℝ (map-f y -ℝ map-f x) (map-f' x *ℝ (yℝ -ℝ xℝ))) *ℝ
                  ( abs-ℝ (map-g x)))
                by
                  preserves-leq-add-ℝ
                    ( triangle-inequality-dist-ℝ _ _ _)
                    ( leq-eq-ℝ (abs-mul-ℝ _ _))
              ≤ ( ( abs-ℝ (map-f y)) *ℝ
                  ( dist-ℝ (map-g y -ℝ map-g x) (map-g' x *ℝ (yℝ -ℝ xℝ)))) +ℝ
                ( ( dist-ℝ (map-f y) (map-f x)) *ℝ
                  ( abs-ℝ (map-g' x *ℝ (yℝ -ℝ xℝ)))) +ℝ
                ( ( abs-ℝ (map-g x)) *ℝ
                  ( dist-ℝ (map-f y -ℝ map-f x) (map-f' x *ℝ (yℝ -ℝ xℝ))))
                by
                  leq-eq-ℝ
                    ( ap-add-ℝ
                      ( ap-add-ℝ
                        ( inv (left-distributive-abs-mul-dist-ℝ _ _ _))
                        ( inv (right-distributive-abs-mul-dist-ℝ _ _ _)))
                      ( commutative-mul-ℝ _ _))
              ≤ ( real-ℚ⁺ M⁺ *ℝ (real-ℚ⁺ (shrink ε) *ℝ dist-ℝ xℝ yℝ)) +ℝ
                ( real-ℚ⁺ (shrink ε) *ℝ (abs-ℝ (map-g' x) *ℝ dist-ℝ yℝ xℝ)) +ℝ
                ( real-ℚ⁺ M⁺ *ℝ (real-ℚ⁺ (shrink ε) *ℝ dist-ℝ xℝ yℝ))
                by
                  preserves-leq-add-ℝ
                    ( preserves-leq-add-ℝ
                      ( preserves-leq-mul-ℝ⁰⁺
                        ( nonnegative-abs-ℝ (map-f y))
                        ( nonnegative-real-ℚ⁺ M⁺)
                        ( nonnegative-dist-ℝ _ _)
                        ( ( nonnegative-real-ℚ⁺ (shrink ε)) *ℝ⁰⁺
                          ( nonnegative-dist-ℝ xℝ yℝ))
                        ( |f|≤M⁺ y)
                        ( is-mod-δg (shrink ε) x y
                          ( weakly-monotonic-neighborhood-ℝ xℝ yℝ (δ ε) _
                            ( δ≤δg-shrink ε)
                            ( Nδxy))))
                      ( preserves-leq-mul-ℝ⁰⁺
                        ( nonnegative-dist-ℝ _ _)
                        ( nonnegative-real-ℚ⁺ (shrink ε))
                        ( nonnegative-abs-ℝ _)
                        ( nonnegative-abs-ℝ _ *ℝ⁰⁺ nonnegative-dist-ℝ _ _)
                        ( leq-dist-neighborhood-ℝ (shrink ε) _ _
                          ( is-mod-ωf y (shrink ε) x
                            ( weakly-monotonic-neighborhood-ℝ yℝ xℝ (δ ε) _
                              ( leq-right-min-ℚ⁺ _ _)
                              ( is-symmetric-neighborhood-ℝ (δ ε) xℝ yℝ Nδxy))))
                        ( leq-eq-ℝ (abs-mul-ℝ _ _))))
                    ( preserves-leq-mul-ℝ⁰⁺
                      ( nonnegative-abs-ℝ (map-g x))
                      ( nonnegative-real-ℚ⁺ M⁺)
                      ( nonnegative-dist-ℝ _ _)
                      ( ( nonnegative-real-ℚ⁺ (shrink ε)) *ℝ⁰⁺
                        ( nonnegative-dist-ℝ xℝ yℝ))
                      ( |g|≤M⁺ x)
                      ( is-mod-δf (shrink ε) x y
                        ( weakly-monotonic-neighborhood-ℝ xℝ yℝ (δ ε) _
                          ( δ≤δf-shrink ε)
                          ( Nδxy))))
              ≤ ( real-ℚ⁺ M⁺ *ℝ (real-ℚ⁺ (shrink ε) *ℝ dist-ℝ xℝ yℝ)) +ℝ
                ( real-ℚ⁺ (shrink ε) *ℝ (real-ℚ⁺ M⁺ *ℝ dist-ℝ yℝ xℝ)) +ℝ
                ( real-ℚ⁺ M⁺ *ℝ (real-ℚ⁺ (shrink ε) *ℝ dist-ℝ xℝ yℝ))
                by
                  preserves-leq-right-add-ℝ _ _ _
                    ( preserves-leq-left-add-ℝ _ _ _
                      ( preserves-leq-left-mul-ℝ⁰⁺
                        ( nonnegative-real-ℚ⁺ (shrink ε))
                        ( preserves-leq-right-mul-ℝ⁰⁺
                          ( nonnegative-dist-ℝ yℝ xℝ)
                          ( |g'|≤M⁺ x))))
              ≤ ( real-ℚ⁺ M⁺ *ℝ (real-ℚ⁺ (shrink ε) *ℝ dist-ℝ xℝ yℝ)) +ℝ
                ( real-ℚ⁺ M⁺ *ℝ (real-ℚ⁺ (shrink ε) *ℝ dist-ℝ xℝ yℝ)) +ℝ
                ( real-ℚ⁺ M⁺ *ℝ (real-ℚ⁺ (shrink ε) *ℝ dist-ℝ xℝ yℝ))
                by
                  leq-eq-ℝ
                    ( ap-add-ℝ
                      ( ap-add-ℝ
                        ( refl)
                        ( ( ap-mul-ℝ
                            ( refl)
                            ( ap-mul-ℝ refl (commutative-dist-ℝ yℝ xℝ))) ∙
                          ( left-swap-mul-ℝ _ _ _)))
                      ( refl))
              ≤ real-ℕ 3 *ℝ (real-ℚ⁺ M⁺ *ℝ (real-ℚ⁺ (shrink ε) *ℝ dist-ℝ xℝ yℝ))
                by leq-eq-ℝ (inv (left-mul-real-ℕ 3 _))
              ≤ ( real-ℚ⁺ (three-ℚ⁺ *ℚ⁺ M⁺)) *ℝ
                ( real-ℚ⁺ (shrink ε) *ℝ dist-ℝ xℝ yℝ)
                by leq-eq-ℝ (combine-left-mul-real-ℚ _ _ _)
              ≤ ( real-ℚ⁺ (three-ℚ⁺ *ℚ⁺ M⁺ *ℚ⁺ shrink ε)) *ℝ dist-ℝ xℝ yℝ
                by leq-eq-ℝ (combine-left-mul-real-ℚ _ _ _)
              ≤ real-ℚ⁺ ε *ℝ dist-ℝ xℝ yℝ
                by
                  leq-eq-ℝ
                    ( ap-mul-ℝ
                      ( ap real-ℚ (is-section-left-div-ℚ⁺ _ _))
                      ( refl)))

module _
  {l1 l2 l3 : Level}
  ([a,b] : proper-closed-interval-ℝ l1 l1)
  (f@(map-f , map-f' , Df=f') :
    differentiable-real-map-proper-closed-interval-ℝ l2 [a,b])
  (g@(map-g , map-g' , Dg=g') :
    differentiable-real-map-proper-closed-interval-ℝ l3 [a,b])
  where

  map-mul-differentiable-real-map-proper-closed-interval-ℝ :
    type-proper-closed-interval-ℝ l1 [a,b] → ℝ (l2 ⊔ l3)
  map-mul-differentiable-real-map-proper-closed-interval-ℝ x =
    map-f x *ℝ map-g x

  map-derivative-mul-differentiable-real-map-proper-closed-interval-ℝ :
    type-proper-closed-interval-ℝ l1 [a,b] → ℝ (l1 ⊔ l2 ⊔ l3)
  map-derivative-mul-differentiable-real-map-proper-closed-interval-ℝ x =
    map-f x *ℝ map-g' x +ℝ map-f' x *ℝ map-g x

  is-differentiable-map-mul-differentiable-real-map-proper-closed-interval-ℝ :
    is-differentiable-real-map-proper-closed-interval-ℝ
      ( [a,b])
      ( map-mul-differentiable-real-map-proper-closed-interval-ℝ)
  is-differentiable-map-mul-differentiable-real-map-proper-closed-interval-ℝ =
    ( map-derivative-mul-differentiable-real-map-proper-closed-interval-ℝ ,
      is-derivative-mul-uniformly-continuous-real-map-proper-closed-interval-ℝ
        ( [a,b])
        ( uniformly-continuous-map-differentiable-real-map-proper-closed-interval-ℝ
          ( [a,b])
          ( f))
        ( uniformly-continuous-map-differentiable-real-map-proper-closed-interval-ℝ
          ( [a,b])
          ( g))
        ( uniformly-continuous-map-derivative-differentiable-real-map-proper-closed-interval-ℝ
          ( [a,b])
          ( f))
        ( uniformly-continuous-map-derivative-differentiable-real-map-proper-closed-interval-ℝ
          ( [a,b])
          ( g))
        ( Df=f')
        ( Dg=g'))
```

## External links

- [Product rule](https://en.wikipedia.org/wiki/Product_rule) on Wikipedia
