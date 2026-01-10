# Pointwise continuous endomaps on the real numbers

```agda
module real-numbers.pointwise-continuous-endomaps-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.axiom-of-countable-choice
open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import metric-spaces.pointwise-continuous-maps-metric-spaces

open import real-numbers.dedekind-real-numbers
open import real-numbers.limits-of-endomaps-real-numbers
open import real-numbers.metric-space-of-real-numbers
```

</details>

## Idea

A
{{#concept "pointwise continuous" Disambiguation="endomap on ℝ" Agda=pointwise-continuous-endomap-ℝ}}
[endomorphism](foundation.endomorphisms.md) on the
[real numbers](real-numbers.dedekind-real-numbers.md)
[pointwise continuous map](metric-spaces.pointwise-continuous-maps-metric-spaces.md)
from the
[metric space of real numbers](real-numbers.metric-space-of-real-numbers.md) to
itself.

## Definition

```agda
is-pointwise-continuous-prop-function-ℝ :
  {l1 l2 : Level} → (ℝ l1 → ℝ l2) → Prop (lsuc l1 ⊔ l2)
is-pointwise-continuous-prop-function-ℝ {l1} {l2} =
  is-pointwise-continuous-prop-map-Metric-Space
    ( metric-space-ℝ l1)
    ( metric-space-ℝ l2)

is-pointwise-continuous-endomap-ℝ :
  {l1 l2 : Level} → (ℝ l1 → ℝ l2) → UU (lsuc l1 ⊔ l2)
is-pointwise-continuous-endomap-ℝ f =
  type-Prop (is-pointwise-continuous-prop-function-ℝ f)

pointwise-continuous-endomap-ℝ : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
pointwise-continuous-endomap-ℝ l1 l2 =
  type-subtype (is-pointwise-continuous-prop-function-ℝ {l1} {l2})

module _
  {l1 l2 : Level}
  (f : pointwise-continuous-endomap-ℝ l1 l2)
  where

  map-pointwise-continuous-endomap-ℝ : ℝ l1 → ℝ l2
  map-pointwise-continuous-endomap-ℝ = pr1 f

  is-pointwise-continuous-map-pointwise-continuous-endomap-ℝ :
    is-pointwise-continuous-endomap-ℝ map-pointwise-continuous-endomap-ℝ
  is-pointwise-continuous-map-pointwise-continuous-endomap-ℝ = pr2 f
```

## See also

- [Pointwise ε-δ continuous endomaps on the real numbers](real-numbers.pointwise-epsilon-delta-continuous-endomaps-real-numbers.md)
