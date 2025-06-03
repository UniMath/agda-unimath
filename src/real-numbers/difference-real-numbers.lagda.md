# The difference between real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.difference-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.difference-rational-numbers
open import elementary-number-theory.rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-real-numbers
```

</details>

## Idea

The {{#concept "difference" Disambiguation="real numbers" Agda=diff-ℝ}} of two
[real numbers](real-numbers.dedekind-real-numbers.md) `x` and `y` is the sum of
`x` and the [negation](real-numbers.negation-real-numbers.md) of `y`.

## Definition

```agda
diff-ℝ : {l1 l2 : Level} → (x : ℝ l1) → (y : ℝ l2) → ℝ (l1 ⊔ l2)
diff-ℝ x y = add-ℝ x (neg-ℝ y)

infixl 36 _-ℝ_
_-ℝ_ = diff-ℝ
```

## Properties

### The inclusion of rational numbers preserves differences

```agda
abstract
  diff-real-ℚ : (p q : ℚ) → (real-ℚ p) -ℝ (real-ℚ q) ＝ real-ℚ (p -ℚ q)
  diff-real-ℚ p q = ap (real-ℚ p +ℝ_) (neg-real-ℚ q) ∙ add-real-ℚ p (neg-ℚ q)
```

### The negative of the difference of `x` and `y` is the difference of `y` and `x`

```agda
module _
  {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2)
  where

  abstract
    distributive-neg-diff-ℝ : neg-ℝ (x -ℝ y) ＝ y -ℝ x
    distributive-neg-diff-ℝ =
      equational-reasoning
        neg-ℝ (x -ℝ y)
        ＝ neg-ℝ x +ℝ neg-ℝ (neg-ℝ y) by distributive-neg-add-ℝ _ _
        ＝ neg-ℝ x +ℝ y by ap (neg-ℝ x +ℝ_) (neg-neg-ℝ y)
        ＝ y -ℝ x by commutative-add-ℝ _ _
```

### Interchange laws for addition and difference on real numbers

```agda
module _
  {l1 l2 l3 l4 : Level} (a : ℝ l1) (b : ℝ l2) (c : ℝ l3) (d : ℝ l4)
  where

  abstract
    interchange-law-diff-add-ℝ :
      (a +ℝ b) -ℝ (c +ℝ d) ＝ (a -ℝ c) +ℝ (b -ℝ d)
    interchange-law-diff-add-ℝ =
      ( ap ((a +ℝ b) +ℝ_) (distributive-neg-add-ℝ c d)) ∙
      ( interchange-law-add-add-ℝ _ _ _ _)
```
