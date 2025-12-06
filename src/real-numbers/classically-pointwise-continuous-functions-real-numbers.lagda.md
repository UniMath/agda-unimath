# Classically pointwise continuous functions on the real numbers

```agda
module real-numbers.classically-pointwise-continuous-functions-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.axiom-of-countable-choice
open import foundation.propositions
open import foundation.universe-levels

open import metric-spaces.classically-pointwise-continuous-functions-metric-spaces

open import real-numbers.dedekind-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.pointwise-continuous-functions-real-numbers
```

</details>

## Idea

A
{{#concept "classically pointwise continuous function" Disambiguation="from ℝ to ℝ" Agda=is-classically-pointwise-continuous-map-ℝ}}
from the [real numbers](real-numbers.dedekind-real-numbers.md) to themselves is
a
[classically pointwise continuous function](metric-spaces.classically-pointwise-continuous-functions-metric-spaces.md)
from the
[metric space of real numbers](real-numbers.metric-space-of-real-numbers.md) to
itself.

## Definition

```agda
module _
  {l1 l2 : Level}
  (f : ℝ l1 → ℝ l2)
  where

  is-classically-pointwise-continuous-prop-function-ℝ : Prop (lsuc l1 ⊔ l2)
  is-classically-pointwise-continuous-prop-function-ℝ =
    is-classically-pointwise-continuous-prop-function-Metric-Space
      ( metric-space-ℝ l1)
      ( metric-space-ℝ l2)
      ( f)

  is-classically-pointwise-continuous-map-ℝ : UU (lsuc l1 ⊔ l2)
  is-classically-pointwise-continuous-map-ℝ =
    type-Prop is-classically-pointwise-continuous-prop-function-ℝ
```

## Properties

### Constructively pointwise continuous functions are classically pointwise continuous

```agda
module _
  {l1 l2 : Level}
  (f : pointwise-continuous-map-ℝ l1 l2)
  where

  abstract
    is-classically-pointwise-continuous-pointwise-continuous-map-ℝ :
      is-classically-pointwise-continuous-map-ℝ
        ( map-pointwise-continuous-map-ℝ f)
    is-classically-pointwise-continuous-pointwise-continuous-map-ℝ =
      is-classically-pointwise-continuous-pointwise-continuous-map-Metric-Space
        ( metric-space-ℝ l1)
        ( metric-space-ℝ l2)
        ( f)
```

### Assuming countable choice, the classical definition of continuity implies the constructive definition

```agda
module _
  {l1 l2 : Level}
  (acω : ACω)
  (f : ℝ l1 → ℝ l2)
  where

  abstract
    is-pointwise-continuous-is-classically-pointwise-continuous-ACω-function-ℝ :
      is-classically-pointwise-continuous-map-ℝ f →
      is-pointwise-continuous-map-ℝ f
    is-pointwise-continuous-is-classically-pointwise-continuous-ACω-function-ℝ =
      is-pointwise-continuous-is-classically-pointwise-continuous-ACω-function-Metric-Space
        ( acω)
        ( metric-space-ℝ l1)
        ( metric-space-ℝ l2)
        ( f)
```

## See also

- [Constructively pointwise continuous functions on the real numbers](real-numbers.pointwise-continuous-functions-real-numbers.md)
