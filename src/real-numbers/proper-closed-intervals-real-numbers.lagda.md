# Proper closed intervals in the real numbers

```agda
module real-numbers.proper-closed-intervals-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import real-numbers.dedekind-real-numbers
open import real-numbers.strict-inequality-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.closed-intervals-real-numbers
open import foundation.universe-levels
open import foundation.dependent-pair-types
```

</details>

## Idea

A
{{#concept "proper closed interval" Disambiguation="in ℝ" Agda=proper-closed-interval-ℝ}}
in the [real numbers](real-numbers.dedekind-real-numbers.md) is a
[closed interval](real-numbers.closed-intervals-real-numbers.md) in which the
lower bound is
[strictly less than](real-numbers.strict-inequality-real-numbers.md) the upper
bound.

## Definition

```agda
proper-closed-interval-ℝ : (l1 l2 : Level) → UU ?
proper-closed-interval-ℝ =
  Σ (ℝ l1) (λ x → Σ (ℝ l2) (λ y → le-ℝ x y))
```
