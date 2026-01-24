# Limits of endomaps on the real numbers

```agda
module real-numbers.limits-of-endomaps-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.propositions
open import foundation.universe-levels

open import metric-spaces.limits-of-maps-metric-spaces

open import real-numbers.dedekind-real-numbers
open import real-numbers.metric-space-of-real-numbers
```

</details>

## Idea

A
{{#concept "limit" Disambiguation="of a function from ℝ to ℝ" Agda=is-limit-endomap-ℝ}}
of an [endomap](foundation.endomorphisms.md) `f` on the
[real numbers](real-numbers.dedekind-real-numbers.md) at `x : ℝ` is the
[limit](metric-spaces.limits-of-maps-metric-spaces.md) of `f` at `x` in the
[metric space of real numbers](real-numbers.metric-space-of-real-numbers.md).

## Definition

```agda
is-limit-prop-endomap-ℝ :
  {l1 l2 : Level} → (ℝ l1 → ℝ l2) → ℝ l1 → ℝ l2 → Prop (lsuc l1 ⊔ l2)
is-limit-prop-endomap-ℝ {l1} {l2} =
  is-point-limit-prop-map-Metric-Space
    ( metric-space-ℝ l1)
    ( metric-space-ℝ l2)

is-limit-endomap-ℝ :
  {l1 l2 : Level} → (ℝ l1 → ℝ l2) → ℝ l1 → ℝ l2 → UU (lsuc l1 ⊔ l2)
is-limit-endomap-ℝ f x y = type-Prop (is-limit-prop-endomap-ℝ f x y)
```
