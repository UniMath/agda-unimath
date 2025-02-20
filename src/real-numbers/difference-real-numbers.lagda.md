# The difference between real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.difference-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.negation-real-numbers
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
