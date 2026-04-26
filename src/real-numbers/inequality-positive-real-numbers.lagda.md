# Inequality of positive real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.inequality-positive-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.propositions
open import foundation.universe-levels

open import real-numbers.inequality-real-numbers
open import real-numbers.positive-real-numbers
```

</details>

## Idea

The
{{#concept "standard ordering" Disambiguation="on the positive real numbers" Agda=leq-ℝ⁺}}
on the [positive real numbers](real-numbers.positive-real-numbers.md) is
inherited from the [standard ordering](real-numbers.inequality-real-numbers.md)
on [real numbers](real-numbers.dedekind-real-numbers.md).

## Definition

```agda
leq-prop-ℝ⁺ : {l1 l2 : Level} → ℝ⁺ l1 → ℝ⁺ l2 → Prop (l1 ⊔ l2)
leq-prop-ℝ⁺ x y = leq-prop-ℝ (real-ℝ⁺ x) (real-ℝ⁺ y)

leq-ℝ⁺ : {l1 l2 : Level} → ℝ⁺ l1 → ℝ⁺ l2 → UU (l1 ⊔ l2)
leq-ℝ⁺ x y = type-Prop (leq-prop-ℝ⁺ x y)
```
