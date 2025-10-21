# Strict inequality of nonnegative real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.strict-inequality-nonnegative-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.propositions
open import foundation.universe-levels

open import real-numbers.dedekind-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.strict-inequality-real-numbers
```

</details>

## Idea

The
{{#concept "standard strict ordering" Disambiguation="on the nonnegative real numbers" Agda=le-ℝ⁰⁺}}
on the [nonnegative real numbers](real-numbers.nonnegative-real-numbers.md) is
inherited from the
[standard strict ordering](real-numbers.strict-inequality-real-numbers.md) on
[real numbers](real-numbers.dedekind-real-numbers.md).

## Definition

```agda
le-prop-ℝ⁰⁺ : {l1 l2 : Level} → ℝ⁰⁺ l1 → ℝ⁰⁺ l2 → Prop (l1 ⊔ l2)
le-prop-ℝ⁰⁺ x y = le-prop-ℝ (real-ℝ⁰⁺ x) (real-ℝ⁰⁺ y)

le-ℝ⁰⁺ : {l1 l2 : Level} → ℝ⁰⁺ l1 → ℝ⁰⁺ l2 → UU (l1 ⊔ l2)
le-ℝ⁰⁺ x y = type-Prop (le-prop-ℝ⁰⁺ x y)
```
