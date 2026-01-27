# Differentiability of constant functions on proper closed intervals in the real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module analysis.differentiability-constant-real-maps-on-proper-closed-intervals-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import analysis.differentiable-real-maps-on-proper-closed-intervals-real-numbers

open import elementary-number-theory.positive-rational-numbers

open import foundation.constant-maps
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import order-theory.large-posets

open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.distance-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.multiplication-nonnegative-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.proper-closed-intervals-real-numbers
open import real-numbers.raising-universe-levels-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-real-numbers
```

</details>

## Idea

Given a
[proper closed interval](real-numbers.proper-closed-intervals-real-numbers.md)
`[a, b]` on the [real numbers](real-numbers.dedekind-real-numbers.md), any
[constant function](foundation.constant-maps.md) on `[a, b]`, `x ↦ c`, is
[differentiable](analysis.differentiable-real-maps-on-proper-closed-intervals-real-numbers.md),
with derivative the constant [zero](real-numbers.zero-real-numbers.md) function.

## Proof

```agda
module _
  {l1 l2 : Level}
  ([a,b] : proper-closed-interval-ℝ l1 l1)
  (c : ℝ l2)
  where

  abstract
    is-derivative-const-zero-const-real-map-proper-closed-interval-ℝ :
      is-derivative-real-map-proper-closed-interval-ℝ
        ( [a,b])
        ( const (type-proper-closed-interval-ℝ l1 [a,b]) c)
        ( const
          ( type-proper-closed-interval-ℝ l1 [a,b])
          ( raise-zero-ℝ (l1 ⊔ l2)))
    is-derivative-const-zero-const-real-map-proper-closed-interval-ℝ =
      let
        open inequality-reasoning-Large-Poset ℝ-Large-Poset
      in
        is-derivative-modulus-of-real-map-proper-closed-interval-ℝ [a,b]
          ( _)
          ( _)
          ( λ ε →
            ( one-ℚ⁺ ,
              λ x y _ →
              chain-of-inequalities
                dist-ℝ (c -ℝ c) (raise-zero-ℝ (l1 ⊔ l2) *ℝ (pr1 y -ℝ pr1 x))
                ≤ dist-ℝ zero-ℝ zero-ℝ
                  by
                    leq-sim-ℝ
                      ( preserves-dist-sim-ℝ
                        ( right-inverse-law-add-ℝ c)
                        ( similarity-reasoning-ℝ
                          raise-zero-ℝ (l1 ⊔ l2) *ℝ (pr1 y -ℝ pr1 x)
                          ~ℝ zero-ℝ *ℝ (pr1 y -ℝ pr1 x)
                            by
                              preserves-sim-right-mul-ℝ _ _ _
                                ( symmetric-sim-ℝ (sim-raise-ℝ _ zero-ℝ))
                          ~ℝ zero-ℝ
                            by left-zero-law-mul-ℝ _))
                ≤ zero-ℝ
                  by leq-sim-ℝ (diagonal-dist-ℝ zero-ℝ)
                ≤ real-ℚ⁺ ε *ℝ dist-ℝ (pr1 x) (pr1 y)
                  by
                    is-nonnegative-real-ℝ⁰⁺
                      ( nonnegative-real-ℚ⁺ ε *ℝ⁰⁺ nonnegative-dist-ℝ _ _)))

differentiable-const-real-map-proper-closed-interval-ℝ :
  {l1 l2 : Level} ([a,b] : proper-closed-interval-ℝ l1 l1) (c : ℝ l2) →
  differentiable-real-map-proper-closed-interval-ℝ l2 [a,b]
differentiable-const-real-map-proper-closed-interval-ℝ {l1} {l2} [a,b] c =
  ( const (type-proper-closed-interval-ℝ l1 [a,b]) c ,
    const (type-proper-closed-interval-ℝ l1 [a,b]) (raise-zero-ℝ (l1 ⊔ l2)) ,
    is-derivative-const-zero-const-real-map-proper-closed-interval-ℝ [a,b] c)
```
