# Maxima and minima of real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.maxima-minima-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.rational-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.functoriality-disjunction
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import real-numbers.dedekind-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.maximum-real-numbers
open import real-numbers.minimum-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.similarity-real-numbers
```

</details>

## Idea

This file contains identities relating to both
[maxima](real-numbers.maximum-real-numbers.md) and
[minima](real-numbers.minimum-real-numbers.md) of
[real numbers](real-numbers.dedekind-real-numbers.md).

## Properties

### `-(max a b) = min (-a) (-b)`

```agda
module _
  {l1 l2 : Level} (a : ℝ l1) (b : ℝ l2)
  where

  abstract
    leq-max-neg-min-neg-ℝ :
      leq-ℝ (max-ℝ a b) (neg-ℝ (min-ℝ (neg-ℝ a) (neg-ℝ b)))
    leq-max-neg-min-neg-ℝ q q<max =
      map-disjunction
        ( lower-cut-ℝ a q)
        ( lower-cut-ℝ a (neg-ℚ (neg-ℚ q)))
        ( lower-cut-ℝ b q)
        ( lower-cut-ℝ b (neg-ℚ (neg-ℚ q)))
        ( inv-tr (is-in-lower-cut-ℝ a) (neg-neg-ℚ q))
        ( inv-tr (is-in-lower-cut-ℝ b) (neg-neg-ℚ q))
        ( q<max)

    leq-neg-min-neg-max-ℝ :
      leq-ℝ (neg-ℝ (min-ℝ (neg-ℝ a) (neg-ℝ b))) (max-ℝ a b)
    leq-neg-min-neg-max-ℝ q q<-min- =
      map-disjunction
        ( lower-cut-ℝ a (neg-ℚ (neg-ℚ q)))
        ( lower-cut-ℝ a q)
        ( lower-cut-ℝ b (neg-ℚ (neg-ℚ q)))
        ( lower-cut-ℝ b q)
        ( tr (is-in-lower-cut-ℝ a) (neg-neg-ℚ q))
        ( tr (is-in-lower-cut-ℝ b) (neg-neg-ℚ q))
        ( q<-min-)

    neg-max-ℝ : neg-ℝ (max-ℝ a b) ＝ min-ℝ (neg-ℝ a) (neg-ℝ b)
    neg-max-ℝ =
      ap
        ( neg-ℝ)
        ( antisymmetric-leq-ℝ
          ( max-ℝ a b)
          ( neg-ℝ (min-ℝ (neg-ℝ a) (neg-ℝ b)))
          ( leq-max-neg-min-neg-ℝ)
          ( leq-neg-min-neg-max-ℝ)) ∙
      neg-neg-ℝ _
```

### `-(min a b) = max (-a) (-b)`

```agda
module _
  {l1 l2 : Level} (a : ℝ l1) (b : ℝ l2)
  where

  abstract
    neg-min-ℝ : neg-ℝ (min-ℝ a b) ＝ max-ℝ (neg-ℝ a) (neg-ℝ b)
    neg-min-ℝ =
      equational-reasoning
        neg-ℝ (min-ℝ a b)
        ＝ neg-ℝ (min-ℝ (neg-ℝ (neg-ℝ a)) (neg-ℝ (neg-ℝ b)))
          by inv (ap neg-ℝ (ap-binary min-ℝ (neg-neg-ℝ a) (neg-neg-ℝ b)))
        ＝ neg-ℝ (neg-ℝ (max-ℝ (neg-ℝ a) (neg-ℝ b)))
          by inv (ap neg-ℝ (neg-max-ℝ _ _))
        ＝ max-ℝ (neg-ℝ a) (neg-ℝ b) by neg-neg-ℝ _
```
