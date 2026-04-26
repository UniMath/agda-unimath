# The composition of differentiable real functions on proper closed intervals in the real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module analysis.composition-differentiable-real-functions-on-proper-closed-intervals-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import analysis.differentiable-real-maps-on-proper-closed-intervals-real-numbers

open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.minimum-positive-rational-numbers
open import elementary-number-theory.minimum-rational-numbers
open import elementary-number-theory.multiplication-positive-rational-numbers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.multiplicative-group-of-positive-rational-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.subtypes
open import foundation.universe-levels

open import order-theory.large-posets

open import real-numbers.absolute-value-real-numbers
open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.distance-real-numbers
open import real-numbers.inequalities-addition-and-subtraction-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.multiplication-nonnegative-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.proper-closed-intervals-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.strict-inequality-real-numbers
open import real-numbers.uniformly-continuous-real-maps-proper-closed-intervals-real-numbers
```

</details>

## Idea

The
{{#concept "chain rule" Disambiguation="on real functions on proper closed intervals in the real numbers"}}
states that given two
[differentiable real maps](analysis.differentiable-real-maps-on-proper-closed-intervals-real-numbers.md)
`f` and `g` on
[proper closed intervals](real-numbers.proper-closed-intervals-real-numbers.md)
`[a, b]` and `[c, d]` in the
[real numbers](real-numbers.dedekind-real-numbers.md), such that `f` maps every
element of `[a, b]` into `[c, d]`, then the
[composition](foundation.function-types.md) `g ∘ f` is differentiable with
derivative `x ↦ g' (f x) * f' x`.

## Proof

This follows the proof of Theorem 6 in Chapter 2 of {{#cite BishopFoundations}}.

```agda
module _
  {l1 l2 l3 : Level}
  ([c,d] : proper-closed-interval-ℝ l2 l2)
  ([a,b] : proper-closed-interval-ℝ l1 l1)
  (g : differentiable-real-map-proper-closed-interval-ℝ (l2 ⊔ l3) [c,d])
  (f : differentiable-real-map-proper-closed-interval-ℝ l2 [a,b])
  (f[a,b]⊆[c,d] :
    subset-im-uniformly-continuous-real-map-proper-closed-interval-ℝ
      ( [a,b])
        ( uniformly-continuous-map-differentiable-real-map-proper-closed-interval-ℝ
          ( [a,b])
          ( f)) ⊆
    subtype-proper-closed-interval-ℝ l2 [c,d])
  where

  map-comp-differentiable-real-map-proper-closed-interval-ℝ :
    type-proper-closed-interval-ℝ l1 [a,b] → ℝ (l2 ⊔ l3)
  map-comp-differentiable-real-map-proper-closed-interval-ℝ x =
    map-differentiable-real-map-proper-closed-interval-ℝ
      ( [c,d])
      ( g)
      ( tot
        ( f[a,b]⊆[c,d])
        ( map-unit-im-uniformly-continuous-real-map-proper-closed-interval-ℝ
          ( [a,b])
          ( uniformly-continuous-map-differentiable-real-map-proper-closed-interval-ℝ
            ( [a,b])
            ( f))
          ( x)))

  map-derivative-comp-differentiable-real-map-proper-closed-interval-ℝ :
    type-proper-closed-interval-ℝ l1 [a,b] → ℝ (l1 ⊔ l2 ⊔ l3)
  map-derivative-comp-differentiable-real-map-proper-closed-interval-ℝ x =
    ( map-derivative-differentiable-real-map-proper-closed-interval-ℝ
      ( [c,d])
      ( g)
      ( tot
        ( f[a,b]⊆[c,d])
        ( map-unit-im-uniformly-continuous-real-map-proper-closed-interval-ℝ
          ( [a,b])
          ( uniformly-continuous-map-differentiable-real-map-proper-closed-interval-ℝ
            ( [a,b])
            ( f))
          ( x)))) *ℝ
    map-derivative-differentiable-real-map-proper-closed-interval-ℝ
      ( [a,b])
      ( f)
      ( x)

  abstract
    is-derivative-comp-differentiable-real-map-proper-closed-interval-ℝ :
      is-derivative-real-map-proper-closed-interval-ℝ
        ( [a,b])
        ( map-comp-differentiable-real-map-proper-closed-interval-ℝ)
        ( map-derivative-comp-differentiable-real-map-proper-closed-interval-ℝ)
    is-derivative-comp-differentiable-real-map-proper-closed-interval-ℝ =
      let
        open
          do-syntax-trunc-Prop
            ( is-derivative-prop-real-map-proper-closed-interval-ℝ
              ( [a,b])
              ( map-comp-differentiable-real-map-proper-closed-interval-ℝ)
              ( map-derivative-comp-differentiable-real-map-proper-closed-interval-ℝ))
        open inequality-reasoning-Large-Poset ℝ-Large-Poset
        (max-|f'|⁰⁺@(max-|f'| , _) , is-max-|f'|) =
          nonnegative-upper-bound-abs-im-uniformly-continuous-real-map-proper-closed-interval-ℝ
            ( [a,b])
            ( uniformly-continuous-map-derivative-differentiable-real-map-proper-closed-interval-ℝ
              ( [a,b])
              ( f))
        (max-|g'|⁰⁺@(max-|g'| , _) , is-max-|g'|) =
          nonnegative-upper-bound-abs-im-uniformly-continuous-real-map-proper-closed-interval-ℝ
            ( [c,d])
            ( uniformly-continuous-map-derivative-differentiable-real-map-proper-closed-interval-ℝ
              ( [c,d])
              ( g))
        gf = map-comp-differentiable-real-map-proper-closed-interval-ℝ
        g'f x =
          ( map-derivative-differentiable-real-map-proper-closed-interval-ℝ
            ( [c,d])
            ( g)
            ( tot
              ( f[a,b]⊆[c,d])
              ( map-unit-im-uniformly-continuous-real-map-proper-closed-interval-ℝ
                ( [a,b])
                ( uniformly-continuous-map-differentiable-real-map-proper-closed-interval-ℝ
                  ( [a,b])
                  ( f))
                ( x))))
        f' =
          map-derivative-differentiable-real-map-proper-closed-interval-ℝ
            ( [a,b])
            ( f)
        map-f =
          map-differentiable-real-map-proper-closed-interval-ℝ
            ( [a,b])
            ( f)
        ucont-f =
          uniformly-continuous-map-differentiable-real-map-proper-closed-interval-ℝ
            ( [a,b])
            ( f)
        tot-f z =
          tot
            ( f[a,b]⊆[c,d])
            ( map-unit-im-uniformly-continuous-real-map-proper-closed-interval-ℝ
              ( [a,b])
              ( ucont-f)
              ( z))
      in do
        (δf , is-mod-δf) ←
          is-derivative-map-derivative-differentiable-real-map-proper-closed-interval-ℝ
            ( [a,b])
            ( f)
        (ωf , is-mod-ωf) ←
          is-uniformly-continuous-map-differentiable-real-map-proper-closed-interval-ℝ
            ( [a,b])
            ( f)
        (δg , is-mod-δg) ←
          is-derivative-map-derivative-differentiable-real-map-proper-closed-interval-ℝ
            ( [c,d])
            ( g)
        (p⁺@(p , _) , max-|f'|<p) ←
          exists-greater-positive-rational-ℝ max-|f'|
        (q⁺@(q , _) , max-|g'|<q) ←
          exists-greater-positive-rational-ℝ max-|g'|
        let
          δ ε =
            let
              (ε₁ , ε₂ , ε₁+ε₂=ε) = split-ℚ⁺ ε
              α = inv-ℚ⁺ p⁺ *ℚ⁺ ε₁
              β = inv-ℚ⁺ (α +ℚ⁺ q⁺) *ℚ⁺ ε₂
            in min-ℚ⁺ (ωf (δg α)) (δf β)
        intro-exists
          ( δ)
          ( λ ε x y Nδxy →
            let
              (ε₁ , ε₂ , ε₁+ε₂=ε) = split-ℚ⁺ ε
              α = inv-ℚ⁺ p⁺ *ℚ⁺ ε₁
              β = inv-ℚ⁺ (α +ℚ⁺ q⁺) *ℚ⁺ ε₂
              |fy-fx-f'⟨y-x⟩|≤β|x-y| =
                is-mod-δf
                  ( β)
                  ( x)
                  ( y)
                  ( weakly-monotonic-neighborhood-ℝ _ _
                    ( min-ℚ⁺ (ωf (δg α)) (δf β))
                    ( δf β)
                    ( leq-right-min-ℚ⁺ (ωf (δg α)) (δf β))
                    ( Nδxy))
            in
              chain-of-inequalities
                dist-ℝ (gf y -ℝ gf x) (g'f x *ℝ f' x *ℝ (pr1 y -ℝ pr1 x))
                ≤ ( dist-ℝ
                    ( gf y -ℝ gf x)
                    ( g'f x *ℝ (map-f y -ℝ map-f x))) +ℝ
                  ( dist-ℝ
                    ( g'f x *ℝ (map-f y -ℝ map-f x))
                    ( g'f x *ℝ f' x *ℝ (pr1 y -ℝ pr1 x)))
                  by triangle-inequality-dist-ℝ _ _ _
                ≤ ( dist-ℝ
                    ( gf y -ℝ gf x)
                    ( g'f x *ℝ (map-f y -ℝ map-f x))) +ℝ
                  ( dist-ℝ
                    ( g'f x *ℝ (map-f y -ℝ map-f x))
                    ( g'f x *ℝ (f' x *ℝ (pr1 y -ℝ pr1 x))))
                  by
                    leq-eq-ℝ
                      ( ap-add-ℝ
                        ( refl)
                        ( ap-dist-ℝ refl (associative-mul-ℝ _ _ _)))
                ≤ ( dist-ℝ
                    ( gf y -ℝ gf x)
                    ( g'f x *ℝ (map-f y -ℝ map-f x))) +ℝ
                  ( ( abs-ℝ (g'f x)) *ℝ
                    ( dist-ℝ
                      ( map-f y -ℝ map-f x))
                      ( f' x *ℝ (pr1 y -ℝ pr1 x)))
                  by
                    leq-eq-ℝ
                      ( ap-add-ℝ
                        ( refl)
                        ( inv (left-distributive-abs-mul-dist-ℝ _ _ _)))
                ≤ ( real-ℚ⁺ α *ℝ dist-ℝ (map-f x) (map-f y)) +ℝ
                  ( real-ℚ q *ℝ (real-ℚ⁺ β *ℝ dist-ℝ (pr1 x) (pr1 y)))
                  by
                    preserves-order-add-ℝ
                      ( is-mod-δg
                        ( α)
                        ( tot-f x)
                        ( tot-f y)
                        ( is-mod-ωf
                          ( x)
                          ( δg α)
                          ( y)
                          ( weakly-monotonic-neighborhood-ℝ _ _
                            ( min-ℚ⁺ (ωf (δg α)) (δf β))
                            ( ωf (δg α))
                            ( leq-left-min-ℚ⁺ (ωf (δg α)) (δf β))
                            ( Nδxy))))
                      ( preserves-order-mul-ℝ⁰⁺
                        ( nonnegative-abs-ℝ (g'f x))
                        ( nonnegative-real-ℚ⁺ q⁺)
                        ( nonnegative-dist-ℝ _ _)
                        ( nonnegative-real-ℚ⁺ β *ℝ⁰⁺ nonnegative-dist-ℝ _ _)
                        ( transitive-leq-ℝ _ _ _
                          ( leq-le-ℝ max-|g'|<q)
                          ( is-max-|g'| (tot-f x)))
                        ( |fy-fx-f'⟨y-x⟩|≤β|x-y|))
                ≤ ( ( real-ℚ⁺ α) *ℝ
                    ( ( abs-ℝ (f' x *ℝ (pr1 x -ℝ pr1 y))) +ℝ
                      ( dist-ℝ
                        ( f' x *ℝ (pr1 x -ℝ pr1 y))
                        ( map-f x -ℝ map-f y)))) +ℝ
                  ( (real-ℚ q *ℝ real-ℚ⁺ β) *ℝ dist-ℝ (pr1 x) (pr1 y))
                  by
                    preserves-order-add-ℝ
                      ( preserves-order-left-mul-ℝ⁰⁺
                        ( nonnegative-real-ℚ⁺ α)
                        ( leq-abs-add-abs-dist-ℝ _ (f' x *ℝ (pr1 x -ℝ pr1 y))))
                      ( leq-eq-ℝ (inv (associative-mul-ℝ _ _ _)))
                ≤ ( ( real-ℚ⁺ α) *ℝ
                    ( ( abs-ℝ (f' x) *ℝ dist-ℝ (pr1 x) (pr1 y)) +ℝ
                      ( dist-ℝ
                        ( neg-ℝ (f' x *ℝ (pr1 x -ℝ pr1 y)))
                        ( neg-ℝ (map-f x -ℝ map-f y))))) +ℝ
                  ( real-ℚ⁺ (q⁺ *ℚ⁺ β) *ℝ dist-ℝ (pr1 x) (pr1 y))
                  by
                    leq-eq-ℝ
                      ( ap-add-ℝ
                        ( ap-mul-ℝ
                          ( refl)
                          ( ap-add-ℝ
                            ( abs-mul-ℝ _ _)
                            ( inv (dist-neg-ℝ _ _))))
                        ( ap-mul-ℝ (mul-real-ℚ _ _) refl))
                ≤ ( ( real-ℚ⁺ α) *ℝ
                    ( ( real-ℚ p *ℝ dist-ℝ (pr1 x) (pr1 y)) +ℝ
                      ( dist-ℝ
                        ( f' x *ℝ neg-ℝ (pr1 x -ℝ pr1 y))
                        ( map-f y -ℝ map-f x)))) +ℝ
                  ( real-ℚ⁺ (q⁺ *ℚ⁺ β) *ℝ dist-ℝ (pr1 x) (pr1 y))
                  by
                    preserves-order-right-add-ℝ _ _ _
                      ( preserves-order-left-mul-ℝ⁰⁺
                        ( nonnegative-real-ℚ⁺ α)
                        ( preserves-order-add-ℝ
                          ( preserves-order-right-mul-ℝ⁰⁺
                            ( nonnegative-dist-ℝ (pr1 x) (pr1 y))
                            ( transitive-leq-ℝ _ _ _
                              ( leq-le-ℝ max-|f'|<p)
                              ( is-max-|f'| x)))
                          ( leq-eq-ℝ
                            ( ap-dist-ℝ
                              ( inv (right-negative-law-mul-ℝ _ _))
                              ( distributive-neg-diff-ℝ (map-f x) (map-f y))))))
                ≤ ( ( real-ℚ⁺ α) *ℝ
                    ( ( real-ℚ p *ℝ dist-ℝ (pr1 x) (pr1 y)) +ℝ
                      ( dist-ℝ
                        ( f' x *ℝ (pr1 y -ℝ pr1 x))
                        ( map-f y -ℝ map-f x)))) +ℝ
                  ( real-ℚ⁺ (q⁺ *ℚ⁺ β) *ℝ dist-ℝ (pr1 x) (pr1 y))
                  by
                    leq-eq-ℝ
                      ( ap-add-ℝ
                        ( ap-mul-ℝ
                          ( refl)
                          ( ap-add-ℝ
                            ( refl)
                            ( ap-dist-ℝ
                              ( ap-mul-ℝ
                                ( refl)
                                ( distributive-neg-diff-ℝ (pr1 x) (pr1 y)))
                              ( refl))))
                        ( refl))
                ≤ ( ( real-ℚ⁺ α) *ℝ
                    ( ( real-ℚ p *ℝ dist-ℝ (pr1 x) (pr1 y)) +ℝ
                      ( dist-ℝ
                        ( map-f y -ℝ map-f x)
                        ( f' x *ℝ (pr1 y -ℝ pr1 x))))) +ℝ
                  ( real-ℚ⁺ (q⁺ *ℚ⁺ β) *ℝ dist-ℝ (pr1 x) (pr1 y))
                  by
                    leq-eq-ℝ
                      ( ap-add-ℝ
                        ( ap-mul-ℝ
                          ( refl)
                          ( ap-add-ℝ
                            ( refl)
                            ( commutative-dist-ℝ _ _)))
                        ( refl))
                ≤ ( ( real-ℚ⁺ α) *ℝ
                    ( ( real-ℚ p *ℝ dist-ℝ (pr1 x) (pr1 y)) +ℝ
                      ( real-ℚ⁺ β *ℝ dist-ℝ (pr1 x) (pr1 y)))) +ℝ
                  ( real-ℚ⁺ (q⁺ *ℚ⁺ β) *ℝ dist-ℝ (pr1 x) (pr1 y))
                  by
                    preserves-order-right-add-ℝ _ _ _
                      ( preserves-order-left-mul-ℝ⁰⁺
                        ( nonnegative-real-ℚ⁺ α)
                        ( preserves-order-left-add-ℝ _ _ _
                          ( |fy-fx-f'⟨y-x⟩|≤β|x-y|)))
                ≤ ( ( real-ℚ⁺ α) *ℝ
                    ( ( real-ℚ p +ℝ real-ℚ⁺ β) *ℝ dist-ℝ (pr1 x) (pr1 y))) +ℝ
                  ( real-ℚ⁺ (q⁺ *ℚ⁺ β) *ℝ dist-ℝ (pr1 x) (pr1 y))
                  by
                    leq-eq-ℝ
                      ( ap-add-ℝ
                        ( ap-mul-ℝ
                          ( refl)
                          ( inv (right-distributive-mul-add-ℝ _ _ _)))
                        ( refl))
                ≤ ( ( real-ℚ⁺ α *ℝ (real-ℚ p +ℝ real-ℚ⁺ β)) *ℝ
                    ( dist-ℝ (pr1 x) (pr1 y))) +ℝ
                  ( real-ℚ⁺ (q⁺ *ℚ⁺ β) *ℝ dist-ℝ (pr1 x) (pr1 y))
                  by
                    leq-eq-ℝ (ap-add-ℝ (inv (associative-mul-ℝ _ _ _)) refl)
                ≤ ( ( real-ℚ⁺ α *ℝ (real-ℚ p +ℝ real-ℚ⁺ β)) +ℝ
                    ( real-ℚ⁺ (q⁺ *ℚ⁺ β))) *ℝ
                  ( dist-ℝ (pr1 x) (pr1 y))
                  by leq-eq-ℝ (inv (right-distributive-mul-add-ℝ _ _ _))
                ≤ ( real-ℚ⁺ α *ℝ real-ℚ⁺ (p⁺ +ℚ⁺ β) +ℝ real-ℚ⁺ (q⁺ *ℚ⁺ β)) *ℝ
                  ( dist-ℝ (pr1 x) (pr1 y))
                  by
                    leq-eq-ℝ
                      ( ap-mul-ℝ
                        ( ap-add-ℝ (ap-mul-ℝ refl (add-real-ℚ _ _)) refl)
                        ( refl))
                ≤ ( real-ℚ⁺ (α *ℚ⁺ (p⁺ +ℚ⁺ β)) +ℝ real-ℚ⁺ (q⁺ *ℚ⁺ β)) *ℝ
                  ( dist-ℝ (pr1 x) (pr1 y))
                  by leq-eq-ℝ (ap-mul-ℝ (ap-add-ℝ (mul-real-ℚ _ _) refl) refl)
                ≤ ( real-ℚ⁺ (α *ℚ⁺ (p⁺ +ℚ⁺ β) +ℚ⁺ q⁺ *ℚ⁺ β)) *ℝ
                  ( dist-ℝ (pr1 x) (pr1 y))
                  by leq-eq-ℝ (ap-mul-ℝ (add-real-ℚ _ _) refl)
                ≤ ( real-ℚ⁺ (α *ℚ⁺ p⁺ +ℚ⁺ α *ℚ⁺ β +ℚ⁺ q⁺ *ℚ⁺ β)) *ℝ
                  ( dist-ℝ (pr1 x) (pr1 y))
                  by
                    leq-eq-ℝ
                      ( ap-mul-ℝ
                        ( ap
                          ( real-ℚ)
                          ( ap-add-ℚ (left-distributive-mul-add-ℚ _ _ _) refl))
                        ( refl))
                ≤ ( real-ℚ⁺ (α *ℚ⁺ p⁺ +ℚ⁺ (α *ℚ⁺ β +ℚ⁺ q⁺ *ℚ⁺ β))) *ℝ
                  ( dist-ℝ (pr1 x) (pr1 y))
                  by
                    leq-eq-ℝ
                      ( ap-mul-ℝ
                        ( ap
                          ( real-ℚ)
                          ( associative-add-ℚ _ _ _))
                        ( refl))
                ≤ ( real-ℚ⁺ (p⁺ *ℚ⁺ α +ℚ⁺ (α +ℚ⁺ q⁺) *ℚ⁺ β)) *ℝ
                  ( dist-ℝ (pr1 x) (pr1 y))
                  by
                    leq-eq-ℝ
                      ( ap-mul-ℝ
                        ( ap
                          ( real-ℚ)
                          ( ap-add-ℚ
                            ( commutative-mul-ℚ _ _)
                            ( inv (right-distributive-mul-add-ℚ _ _ _))))
                        ( refl))
                ≤ real-ℚ⁺ (ε₁ +ℚ⁺ ε₂) *ℝ dist-ℝ (pr1 x) (pr1 y)
                  by
                    leq-eq-ℝ
                      ( ap-mul-ℝ
                        ( ap
                          ( real-ℚ)
                          ( ap-add-ℚ
                            ( is-section-left-div-ℚ⁺ p⁺ _)
                            ( is-section-left-div-ℚ⁺ (α +ℚ⁺ q⁺) _)))
                        ( refl))
                ≤ real-ℚ⁺ ε *ℝ dist-ℝ (pr1 x) (pr1 y)
                  by leq-eq-ℝ (ap-mul-ℝ (ap real-ℚ⁺ ε₁+ε₂=ε) refl))

  is-differentiable-comp-differentiable-real-map-proper-closed-interval-ℝ :
    is-differentiable-real-map-proper-closed-interval-ℝ
      ( [a,b])
      ( map-comp-differentiable-real-map-proper-closed-interval-ℝ)
  is-differentiable-comp-differentiable-real-map-proper-closed-interval-ℝ =
    ( map-derivative-comp-differentiable-real-map-proper-closed-interval-ℝ ,
      is-derivative-comp-differentiable-real-map-proper-closed-interval-ℝ)

  comp-differentiable-real-map-proper-closed-interval-ℝ :
    differentiable-real-map-proper-closed-interval-ℝ (l2 ⊔ l3) [a,b]
  comp-differentiable-real-map-proper-closed-interval-ℝ =
    ( map-comp-differentiable-real-map-proper-closed-interval-ℝ ,
      is-differentiable-comp-differentiable-real-map-proper-closed-interval-ℝ)
```

## References

{{#bibliography}}

## External links

- [Chain rule](https://en.wikipedia.org/wiki/Chain_rule) on Wikipedia
