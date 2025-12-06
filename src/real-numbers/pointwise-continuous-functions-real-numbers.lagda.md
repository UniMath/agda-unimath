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
{{#concept "pointwise continuous function" Disambiguation="from ℝ to ℝ" Agda=pointwise-continuous-map-ℝ}}
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

is-pointwise-continuous-map-ℝ :
  {l1 l2 : Level} → (ℝ l1 → ℝ l2) → UU (lsuc l1 ⊔ l2)
is-pointwise-continuous-map-ℝ f =
  type-Prop (is-pointwise-continuous-prop-function-ℝ f)

pointwise-continuous-map-ℝ : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
pointwise-continuous-map-ℝ l1 l2 =
  type-subtype (is-pointwise-continuous-prop-function-ℝ {l1} {l2})

module _
  {l1 l2 : Level}
  (f : pointwise-continuous-map-ℝ l1 l2)
  where

  map-pointwise-continuous-map-ℝ : ℝ l1 → ℝ l2
  map-pointwise-continuous-map-ℝ = pr1 f

  is-pointwise-continuous-map-pointwise-continuous-map-ℝ :
    is-pointwise-continuous-map-ℝ map-pointwise-continuous-map-ℝ
  is-pointwise-continuous-map-pointwise-continuous-map-ℝ = pr2 f
```

## See also

- [Classically pointwise continuous functions on the real numbers](real-numbers.classically-pointwise-continuous-functions-real-numbers.md)
