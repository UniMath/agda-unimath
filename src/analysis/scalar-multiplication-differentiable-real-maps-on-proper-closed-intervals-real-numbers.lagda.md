# Scalar multiplication of differentiable functions on proper closed intervals in the real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module analysis.scalar-multiplication-differentiable-real-maps-on-proper-closed-intervals-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import analysis.differentiable-real-maps-on-proper-closed-intervals-real-numbers

open import elementary-number-theory.multiplication-positive-rational-numbers
open import elementary-number-theory.multiplicative-group-of-positive-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.universe-levels

open import group-theory.abelian-groups

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

Given a
[differentiable](analysis.differentiable-real-maps-on-proper-closed-intervals-real-numbers.md)
function `f` from a
[proper closed interval](real-numbers.proper-closed-intervals-real-numbers.md)
in the [real numbers](real-numbers.dedekind-real-numbers.md) to the real numbers
with derivative `f'`, and a real number `c`, the map `x ↦ c * f x` is
differentiable with derivative `x ↦ c * f' x`.

## Proof

```agda
module _
  {l1 l2 l3 : Level}
  ([a,b] : proper-closed-interval-ℝ l1 l1)
  (f : type-proper-closed-interval-ℝ l1 [a,b] → ℝ l2)
  (f' : type-proper-closed-interval-ℝ l1 [a,b] → ℝ (l1 ⊔ l2))
  (is-derivative-f-f' :
    is-derivative-real-map-proper-closed-interval-ℝ [a,b] f f')
  (c : ℝ l3)
  where

  abstract
    is-derivative-scalar-mul-real-map-proper-closed-interval-ℝ :
      is-derivative-real-map-proper-closed-interval-ℝ
        ( [a,b])
        ( λ x → c *ℝ f x)
        ( λ x → c *ℝ f' x)
    is-derivative-scalar-mul-real-map-proper-closed-interval-ℝ =
      let
        open
          do-syntax-trunc-Prop
            ( is-derivative-prop-real-map-proper-closed-interval-ℝ
              ( [a,b])
              ( λ x → c *ℝ f x)
              ( λ x → c *ℝ f' x))
        open inequality-reasoning-Large-Poset ℝ-Large-Poset
      in do
        (μ , is-mod-μ) ← is-derivative-f-f'
        (q , |c|<q) ← exists-greater-positive-rational-ℝ (abs-ℝ c)
        is-derivative-modulus-of-real-map-proper-closed-interval-ℝ [a,b]
          ( _)
          ( _)
          ( λ ε →
            ( μ (ε *ℚ⁺ inv-ℚ⁺ q) ,
              λ x y N⟨ε/q⟩xy →
              chain-of-inequalities
                dist-ℝ (c *ℝ f y -ℝ c *ℝ f x) (c *ℝ f' x *ℝ (pr1 y -ℝ pr1 x))
                ≤ dist-ℝ (c *ℝ (f y -ℝ f x)) (c *ℝ (f' x *ℝ (pr1 y -ℝ pr1 x)))
                  by
                    leq-eq-ℝ
                      ( ap-dist-ℝ
                        ( inv (left-distributive-mul-diff-ℝ _ _ _))
                        ( associative-mul-ℝ _ _ _))
                ≤ abs-ℝ c *ℝ dist-ℝ (f y -ℝ f x) (f' x *ℝ (pr1 y -ℝ pr1 x))
                  by leq-eq-ℝ (inv (left-distributive-abs-mul-dist-ℝ _ _ _))
                ≤ ( real-ℚ⁺ q) *ℝ
                  ( real-ℚ⁺ (ε *ℚ⁺ inv-ℚ⁺ q) *ℝ dist-ℝ (pr1 x) (pr1 y))
                  by
                    preserves-leq-mul-ℝ⁰⁺
                      ( nonnegative-abs-ℝ c)
                      ( nonnegative-real-ℚ⁺ q)
                      ( nonnegative-dist-ℝ _ _)
                      ( nonnegative-real-ℚ⁺ (ε *ℚ⁺ inv-ℚ⁺ q) *ℝ⁰⁺
                        nonnegative-dist-ℝ _ _)
                      ( leq-le-ℝ |c|<q)
                      ( is-mod-μ
                        ( ε *ℚ⁺ inv-ℚ⁺ q)
                        ( x)
                        ( y)
                        ( N⟨ε/q⟩xy))
                ≤ real-ℚ⁺ ε *ℝ dist-ℝ (pr1 x) (pr1 y)
                  by
                    leq-eq-ℝ
                      ( ( inv (associative-mul-ℝ _ _ _)) ∙
                        ( ap-mul-ℝ
                          ( ( mul-real-ℚ _ _) ∙
                            ( ap
                              ( real-ℚ⁺)
                              ( is-identity-right-conjugation-Ab
                                ( abelian-group-mul-ℚ⁺)
                                ( q)
                                ( ε))))
                          ( refl)))))

scalar-mul-differentiable-real-map-proper-closed-interval-ℝ :
  {l1 l2 l3 : Level} ([a,b] : proper-closed-interval-ℝ l1 l1) →
  ℝ l2 → differentiable-real-map-proper-closed-interval-ℝ l3 [a,b] →
  differentiable-real-map-proper-closed-interval-ℝ (l2 ⊔ l3) [a,b]
scalar-mul-differentiable-real-map-proper-closed-interval-ℝ
  [a,b] c (f , f' , Df=f') =
  ( ( λ x → c *ℝ f x) ,
    ( λ x → c *ℝ f' x) ,
    is-derivative-scalar-mul-real-map-proper-closed-interval-ℝ
      ( [a,b])
      ( f)
      ( f')
      ( Df=f')
      ( c))
```
