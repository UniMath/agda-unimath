# ε-δ limits of functions on the real numbers

```agda
module real-numbers.epsilon-delta-limits-of-functions-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.axiom-of-countable-choice
open import foundation.propositions
open import foundation.universe-levels

open import metric-spaces.epsilon-delta-limits-of-functions-metric-spaces

open import real-numbers.dedekind-real-numbers
open import real-numbers.limits-of-functions-real-numbers
open import real-numbers.metric-space-of-real-numbers
```

</details>

## Idea

The
{{#concept "ε-δ definition of a limit" Disambiguation="in ℝ" Agda=is-ε-δ-limit-map-ℝ}}
states that the limit of `f x` as `x` approaches `x₀` is a `y` such that for any
`ε : ℚ⁺`, there [exists](foundation.existential-quantification.md) a `δ : ℚ⁺`
such that if `x` and `x₀` are in a `δ`-neighborhood of each other, `f x` and `y`
are in a `ε`-neighborhood of each other.

## Definition

```agda
is-ε-δ-limit-prop-map-ℝ :
  {l1 l2 : Level} → (ℝ l1 → ℝ l2) → ℝ l1 → ℝ l2 → Prop (lsuc l1 ⊔ l2)
is-ε-δ-limit-prop-map-ℝ {l1} {l2} =
  is-ε-δ-limit-prop-map-Metric-Space
    ( metric-space-ℝ l1)
    ( metric-space-ℝ l2)

is-ε-δ-limit-map-ℝ :
  {l1 l2 : Level} → (ℝ l1 → ℝ l2) → ℝ l1 → ℝ l2 → UU (lsuc l1 ⊔ l2)
is-ε-δ-limit-map-ℝ f x y = type-Prop (is-ε-δ-limit-prop-map-ℝ f x y)
```

## Properties

### Constructive limits are classical limits

```agda
module _
  {l1 l2 : Level}
  (f : ℝ l1 → ℝ l2)
  (x : ℝ l1)
  (y : ℝ l2)
  where

  abstract
    is-ε-δ-limit-is-limit-map-ℝ :
      is-limit-function-ℝ f x y → is-ε-δ-limit-map-ℝ f x y
    is-ε-δ-limit-is-limit-map-ℝ =
      is-ε-δ-limit-is-limit-map-Metric-Space
        ( metric-space-ℝ l1)
        ( metric-space-ℝ l2)
        ( f)
        ( x)
        ( y)
```

### Assuming countable choice, classical limits are constructive limits

```agda
module _
  {l1 l2 : Level}
  (acω : ACω)
  (f : ℝ l1 → ℝ l2)
  (x : ℝ l1)
  (y : ℝ l2)
  where

  abstract
    is-limit-is-ε-δ-limit-map-ACω-ℝ :
      is-ε-δ-limit-map-ℝ f x y → is-limit-function-ℝ f x y
    is-limit-is-ε-δ-limit-map-ACω-ℝ =
      is-limit-is-classical-limit-map-acω-Metric-Space
        ( acω)
        ( metric-space-ℝ l1)
        ( metric-space-ℝ l2)
        ( f)
        ( x)
        ( y)
```

## See also

- [Constructive limits of functions on the real numbers](real-numbers.limits-of-functions-real-numbers.md)
