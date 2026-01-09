# Pointwise ε-δ continuous endomaps on the real numbers

```agda
module real-numbers.pointwise-epsilon-delta-continuous-endomaps-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.axiom-of-countable-choice
open import foundation.propositions
open import foundation.universe-levels
open import foundation.dependent-pair-types

open import foundation.subtypes
open import metric-spaces.pointwise-epsilon-delta-continuous-maps-metric-spaces

open import real-numbers.dedekind-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.pointwise-continuous-endomaps-real-numbers
```

</details>

## Idea

A
{{#concept "pointwise ε-δ continuous" Disambiguation="from ℝ to ℝ" Agda=is-pointwise-ε-δ-continuous-endomap-ℝ}}
[endomap](foundation.endomorphisms.md) on the
[real numbers](real-numbers.dedekind-real-numbers.md) to themselves is a
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

  is-pointwise-ε-δ-continuous-prop-endomap-ℝ : Prop (lsuc l1 ⊔ l2)
  is-pointwise-ε-δ-continuous-prop-endomap-ℝ =
    is-pointwise-ε-δ-continuous-prop-map-Metric-Space
      ( metric-space-ℝ l1)
      ( metric-space-ℝ l2)
      ( f)

  is-pointwise-ε-δ-continuous-endomap-ℝ : UU (lsuc l1 ⊔ l2)
  is-pointwise-ε-δ-continuous-endomap-ℝ =
    type-Prop is-pointwise-ε-δ-continuous-prop-endomap-ℝ

pointwise-ε-δ-continuous-endomap-ℝ : (l1 l2 : Level) → UU (lsuc (l1 ⊔ l2))
pointwise-ε-δ-continuous-endomap-ℝ l1 l2 =
  type-subtype (is-pointwise-ε-δ-continuous-prop-endomap-ℝ {l1} {l2})

module _
  {l1 l2 : Level}
  (f : pointwise-ε-δ-continuous-endomap-ℝ l1 l2)
  where

  map-pointwise-ε-δ-continuous-endomap-ℝ : ℝ l1 → ℝ l2
  map-pointwise-ε-δ-continuous-endomap-ℝ = pr1 f

  is-pointwise-ε-δ-continuous-map-pointwise-ε-δ-continuous-endomap-ℝ :
    is-pointwise-ε-δ-continuous-endomap-ℝ map-pointwise-ε-δ-continuous-endomap-ℝ
  is-pointwise-ε-δ-continuous-map-pointwise-ε-δ-continuous-endomap-ℝ = pr2 f
```

## Properties

### Pointwise continuous functions are pointwise ε-δ continuous

```agda
module _
  {l1 l2 : Level}
  (f : pointwise-continuous-endomap-ℝ l1 l2)
  where

  abstract
    is-pointwise-ε-δ-continuous-map-pointwise-continuous-endomap-ℝ :
      is-pointwise-ε-δ-continuous-endomap-ℝ
        ( map-pointwise-continuous-endomap-ℝ f)
    is-pointwise-ε-δ-continuous-map-pointwise-continuous-endomap-ℝ =
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
      is-pointwise-ε-δ-continuous-endomap-ℝ f →
      is-pointwise-continuous-endomap-ℝ f
    is-pointwise-continuous-is-pointwise-ε-δ-continuous-map-ACω-ℝ =
      is-pointwise-continuous-is-pointwise-ε-δ-continuous-map-ACω-Metric-Space
        ( acω)
        ( metric-space-ℝ l1)
        ( metric-space-ℝ l2)
        ( f)
```

## See also

- [Pointwise continuous endomaps on the real numbers](real-numbers.pointwise-continuous-endomaps-real-numbers.md)
