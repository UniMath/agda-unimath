# Limits of functions on the real numbers

```agda
module real-numbers.limits-of-functions-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.axiom-of-countable-choice
open import foundation.propositions
open import foundation.universe-levels

open import metric-spaces.limits-of-functions-metric-spaces

open import real-numbers.dedekind-real-numbers
open import real-numbers.metric-space-of-real-numbers
```

</details>

## Idea

A
{{#concept "limit" Disambiguation="of a function from ℝ to ℝ" Agda=is-limit-function-ℝ}}
of a function `f` from the [real numbers](real-numbers.dedekind-real-numbers.md)
to themselves at `x : ℝ` is the
[limit](metric-spaces.limits-of-functions-metric-spaces.md) of `f` at `x` in the
[metric space of real numbers](real-numbers.metric-space-of-real-numbers.md).

## Definition

```agda
is-limit-prop-function-ℝ :
  {l1 l2 : Level} → (ℝ l1 → ℝ l2) → ℝ l1 → ℝ l2 → Prop (lsuc l1 ⊔ l2)
is-limit-prop-function-ℝ {l1} {l2} =
  is-point-limit-prop-function-Metric-Space
    ( metric-space-ℝ l1)
    ( metric-space-ℝ l2)

is-limit-function-ℝ :
  {l1 l2 : Level} → (ℝ l1 → ℝ l2) → ℝ l1 → ℝ l2 → UU (lsuc l1 ⊔ l2)
is-limit-function-ℝ f x y = type-Prop (is-limit-prop-function-ℝ f x y)
```

### The classical epsilon-delta definition of limit

The
{{#concept "classical definition of a limit" Disambiguation="in ℝ" Agda=is-classical-limit-function-ℝ}}
states that the limit of `f x` as `x` approaches `x₀` is a `y` such that for any
`ε : ℚ⁺`, there [exists](foundation.existential-quantification.md) a `δ : ℚ⁺`
such that if `x` and `x₀` are in a `δ`-neighborhood of each other, `f x` and `y`
are in a `ε`-neighborhood of each other.

```agda
is-classical-limit-prop-function-ℝ :
  {l1 l2 : Level} → (ℝ l1 → ℝ l2) → ℝ l1 → ℝ l2 → Prop (lsuc l1 ⊔ l2)
is-classical-limit-prop-function-ℝ {l1} {l2} =
  is-classical-limit-prop-function-Metric-Space
    ( metric-space-ℝ l1)
    ( metric-space-ℝ l2)

is-classical-limit-function-ℝ :
  {l1 l2 : Level} → (ℝ l1 → ℝ l2) → ℝ l1 → ℝ l2 → UU (lsuc l1 ⊔ l2)
is-classical-limit-function-ℝ f x y =
  type-Prop (is-classical-limit-prop-function-ℝ f x y)
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
    is-classical-limit-is-limit-function-ℝ :
      is-limit-function-ℝ f x y → is-classical-limit-function-ℝ f x y
    is-classical-limit-is-limit-function-ℝ =
      is-classical-limit-is-limit-function-Metric-Space
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
    is-limit-is-classical-limit-ACω-function-ℝ :
      is-classical-limit-function-ℝ f x y → is-limit-function-ℝ f x y
    is-limit-is-classical-limit-ACω-function-ℝ =
      is-limit-is-classical-limit-ACω-function-Metric-Space
        ( acω)
        ( metric-space-ℝ l1)
        ( metric-space-ℝ l2)
        ( f)
        ( x)
        ( y)
```
