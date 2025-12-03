# Pointwise continuous functions on the real numbers

```agda
module real-numbers.pointwise-continuous-functions-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.axiom-of-countable-choice
open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import metric-spaces.pointwise-continuous-functions-metric-spaces

open import real-numbers.dedekind-real-numbers
open import real-numbers.limits-of-functions-real-numbers
open import real-numbers.metric-space-of-real-numbers
```

</details>

## Idea

A
{{#concept "pointwise continuous function" Disambiguation="from ℝ to ℝ" Agda=pointwise-continuous-function-ℝ}}
from the [real numbers](real-numbers.dedekind-real-numbers.md) to the real
numbers is a
[pointwise continuous function](metric-spaces.pointwise-continuous-functions-metric-spaces.md)
from the
[metric space of real numbers](real-numbers.metric-space-of-real-numbers.md) to
itself.

## Definition

```agda
is-pointwise-continuous-prop-function-ℝ :
  {l1 l2 : Level} → (ℝ l1 → ℝ l2) → Prop (lsuc l1 ⊔ l2)
is-pointwise-continuous-prop-function-ℝ {l1} {l2} =
  is-pointwise-continuous-prop-function-Metric-Space
    ( metric-space-ℝ l1)
    ( metric-space-ℝ l2)

is-pointwise-continuous-function-ℝ :
  {l1 l2 : Level} → (ℝ l1 → ℝ l2) → UU (lsuc l1 ⊔ l2)
is-pointwise-continuous-function-ℝ f =
  type-Prop (is-pointwise-continuous-prop-function-ℝ f)

pointwise-continuous-function-ℝ : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
pointwise-continuous-function-ℝ l1 l2 =
  type-subtype (is-pointwise-continuous-prop-function-ℝ {l1} {l2})

module _
  {l1 l2 : Level}
  (f : pointwise-continuous-function-ℝ l1 l2)
  where

  map-pointwise-continuous-function-ℝ : ℝ l1 → ℝ l2
  map-pointwise-continuous-function-ℝ = pr1 f

  is-pointwise-continuous-map-pointwise-continuous-function-ℝ :
    is-pointwise-continuous-function-ℝ map-pointwise-continuous-function-ℝ
  is-pointwise-continuous-map-pointwise-continuous-function-ℝ = pr2 f
```

### The classical definition of pointwise continuity

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

  is-classically-pointwise-continuous-function-ℝ : UU (lsuc l1 ⊔ l2)
  is-classically-pointwise-continuous-function-ℝ =
    type-Prop is-classically-pointwise-continuous-prop-function-ℝ
```

## Properties

### Constructively pointwise continuous functions are classically pointwise continuous

```agda
module _
  {l1 l2 : Level}
  (f : pointwise-continuous-function-ℝ l1 l2)
  where

  abstract
    is-classically-pointwise-continuous-pointwise-continuous-function-ℝ :
      is-classically-pointwise-continuous-function-ℝ
        ( map-pointwise-continuous-function-ℝ f)
    is-classically-pointwise-continuous-pointwise-continuous-function-ℝ =
      is-classically-pointwise-continuous-pointwise-continuous-function-Metric-Space
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
      is-classically-pointwise-continuous-function-ℝ f →
      is-pointwise-continuous-function-ℝ f
    is-pointwise-continuous-is-classically-pointwise-continuous-ACω-function-ℝ =
      is-pointwise-continuous-is-classically-pointwise-continuous-ACω-function-Metric-Space
        ( acω)
        ( metric-space-ℝ l1)
        ( metric-space-ℝ l2)
        ( f)
```
