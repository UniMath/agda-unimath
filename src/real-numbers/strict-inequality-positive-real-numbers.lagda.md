# Strict inequality of positive real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.strict-inequality-positive-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.propositions
open import foundation.universe-levels

open import real-numbers.dedekind-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.strict-inequality-real-numbers
```

</details>

## Idea

The
{{#concept "standard strict ordering" Disambiguation="on the positive real numbers" Agda=le-ℝ⁺}}
on the [positive real numbers](real-numbers.positive-real-numbers.md) is
inherited from the
[standard strict ordering](real-numbers.strict-inequality-real-numbers.md) on
[real numbers](real-numbers.dedekind-real-numbers.md).

## Definition

```agda
le-prop-ℝ⁺ : {l1 l2 : Level} → ℝ⁺ l1 → ℝ⁺ l2 → Prop (l1 ⊔ l2)
le-prop-ℝ⁺ x y = le-prop-ℝ (real-ℝ⁺ x) (real-ℝ⁺ y)

le-ℝ⁺ : {l1 l2 : Level} → ℝ⁺ l1 → ℝ⁺ l2 → UU (l1 ⊔ l2)
le-ℝ⁺ x y = type-Prop (le-prop-ℝ⁺ x y)
```
