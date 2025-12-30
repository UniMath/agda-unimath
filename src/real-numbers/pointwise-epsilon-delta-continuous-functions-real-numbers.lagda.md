# Pointwise ε-δ continuous functions on the real numbers

```agda
module real-numbers.pointwise-epsilon-delta-continuous-functions-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.axiom-of-countable-choice
open import foundation.propositions
open import foundation.universe-levels

open import metric-spaces.pointwise-epsilon-delta-continuous-functions-metric-spaces

open import real-numbers.dedekind-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.pointwise-continuous-functions-real-numbers
```

</details>

## Idea

A
{{#concept "pointwise ε-δ continuous function" Disambiguation="from ℝ to ℝ" Agda=is-pointwise-ε-δ-continuous-map-ℝ}}
from the [real numbers](real-numbers.dedekind-real-numbers.md) to themselves is
a
[pointwise ε-δ continuous function](metric-spaces.pointwise-epsilon-delta-continuous-functions-metric-spaces.md)
from the
[metric space of real numbers](real-numbers.metric-space-of-real-numbers.md) to
itself.

## Definition

```agda
module _
  {l1 l2 : Level}
  (f : ℝ l1 → ℝ l2)
  where

  is-pointwise-ε-δ-continuous-prop-map-ℝ : Prop (lsuc l1 ⊔ l2)
  is-pointwise-ε-δ-continuous-prop-map-ℝ =
    is-pointwise-ε-δ-continuous-prop-map-Metric-Space
      ( metric-space-ℝ l1)
      ( metric-space-ℝ l2)
      ( f)

  is-pointwise-ε-δ-continuous-map-ℝ : UU (lsuc l1 ⊔ l2)
  is-pointwise-ε-δ-continuous-map-ℝ =
    type-Prop is-pointwise-ε-δ-continuous-prop-map-ℝ
```

## Properties

### Pointwise continuous functions are pointwise ε-δ continuous

```agda
module _
  {l1 l2 : Level}
  (f : pointwise-continuous-map-ℝ l1 l2)
  where

  abstract
    is-pointwise-ε-δ-continuous-map-pointwise-continuous-map-ℝ :
      is-pointwise-ε-δ-continuous-map-ℝ
        ( map-pointwise-continuous-map-ℝ f)
    is-pointwise-ε-δ-continuous-map-pointwise-continuous-map-ℝ =
      is-pointwise-ε-δ-continuous-map-pointwise-continuous-map-Metric-Space
        ( metric-space-ℝ l1)
        ( metric-space-ℝ l2)
        ( f)
```

### Assuming countable choice, pointwise ε-δ continuous functions are pointwise continuous

```agda
module _
  {l1 l2 : Level}
  (acω : ACω)
  (f : ℝ l1 → ℝ l2)
  where

  abstract
    is-pointwise-continuous-is-pointwise-ε-δ-continuous-map-ACω-ℝ :
      is-pointwise-ε-δ-continuous-map-ℝ f →
      is-pointwise-continuous-map-ℝ f
    is-pointwise-continuous-is-pointwise-ε-δ-continuous-map-ACω-ℝ =
      is-pointwise-continuous-is-pointwise-ε-δ-continuous-map-ACω-Metric-Space
        ( acω)
        ( metric-space-ℝ l1)
        ( metric-space-ℝ l2)
        ( f)
```

## See also

- [Constructively pointwise continuous functions on the real numbers](real-numbers.pointwise-continuous-functions-real-numbers.md)
