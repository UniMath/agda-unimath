# Differentiability of the identity function on proper closed intervals in the real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module analysis.differentiability-identity-function-on-proper-closed-intervals-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import analysis.differentiable-real-functions-on-proper-closed-intervals-real-numbers

open import elementary-number-theory.positive-rational-numbers

open import foundation.constant-maps
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import order-theory.large-posets

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
`[a, b]` on the [real numbers](real-numbers.dedekind-real-numbers.md), the
[identity function](foundation.function-types.md) on `[a, b]` is
[differentiable](analysis.differentiable-real-functions-on-proper-closed-intervals-real-numbers.md),
and its derivative is the [constant](foundation.constant-maps.md)
[one](real-numbers.rational-real-numbers.md) function.

### The derivative of the identity function is 1

```agda
module _
  {l : Level}
  ([a,b] : proper-closed-interval-ℝ l l)
  where

  abstract
    derivative-id-real-function-proper-closed-interval-ℝ :
      is-derivative-real-function-proper-closed-interval-ℝ
        ( [a,b])
        ( pr1)
        ( const (type-proper-closed-interval-ℝ l [a,b]) (raise-one-ℝ l))
    derivative-id-real-function-proper-closed-interval-ℝ =
      let
        open inequality-reasoning-Large-Poset ℝ-Large-Poset
      in
        is-derivative-modulus-of-real-function-proper-closed-interval-ℝ [a,b]
          ( _)
          ( _)
          ( λ ε →
            ( one-ℚ⁺ ,
              λ x y _ →
              chain-of-inequalities
                dist-ℝ (pr1 y -ℝ pr1 x) (raise-one-ℝ l *ℝ (pr1 y -ℝ pr1 x))
                ≤ dist-ℝ (pr1 y -ℝ pr1 x) (pr1 y -ℝ pr1 x)
                  by
                    leq-eq-ℝ
                      ( ap-dist-ℝ
                        ( refl)
                        ( ( eq-sim-ℝ
                            ( preserves-sim-right-mul-ℝ _ _ _
                              ( symmetric-sim-ℝ (sim-raise-ℝ _ _)))) ∙
                          ( left-unit-law-mul-ℝ _)))
                ≤ zero-ℝ
                  by leq-sim-ℝ (diagonal-dist-ℝ _)
                ≤ real-ℚ⁺ ε *ℝ dist-ℝ (pr1 x) (pr1 y)
                  by
                    is-nonnegative-real-ℝ⁰⁺
                      ( nonnegative-real-ℚ⁺ ε *ℝ⁰⁺ nonnegative-dist-ℝ _ _)))

differentiable-id-function-proper-closed-interval-ℝ :
  {l : Level} ([a,b] : proper-closed-interval-ℝ l l) →
  differentiable-real-function-proper-closed-interval-ℝ l [a,b]
differentiable-id-function-proper-closed-interval-ℝ {l} [a,b] =
  ( pr1 ,
    ( λ _ → raise-one-ℝ l) ,
    derivative-id-real-function-proper-closed-interval-ℝ [a,b])
```
