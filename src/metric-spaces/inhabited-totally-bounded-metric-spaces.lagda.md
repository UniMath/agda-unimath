# Inhabited, totally bounded metric spaces

```agda
module metric-spaces.inhabited-totally-bounded-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.images
open import foundation.inhabited-types
open import foundation.subtypes
open import foundation.universe-levels

open import metric-spaces.metric-spaces
open import metric-spaces.subspaces-metric-spaces
open import metric-spaces.totally-bounded-metric-spaces
open import metric-spaces.uniformly-continuous-maps-metric-spaces
```

</details>

## Idea

A [metric space](metric-spaces.metric-spaces.md) may be both
[inhabited](foundation.inhabited-types.md) and
[totally bounded](metric-spaces.totally-bounded-metric-spaces.md).

## Definition

```agda
is-inhabited-totally-bounded-prop-Metric-Space :
  {l1 l2 : Level} (l3 : Level) →
  subtype (l1 ⊔ l2 ⊔ lsuc l3) (Metric-Space l1 l2)
is-inhabited-totally-bounded-prop-Metric-Space l3 X =
  is-totally-bounded-prop-Metric-Space l3 X ∧
  is-inhabited-Prop (type-Metric-Space X)

is-inhabited-totally-bounded-Metric-Space :
  {l1 l2 : Level} (l3 : Level) → Metric-Space l1 l2 → UU (l1 ⊔ l2 ⊔ lsuc l3)
is-inhabited-totally-bounded-Metric-Space l3 =
  is-in-subtype (is-inhabited-totally-bounded-prop-Metric-Space l3)

inhabited-totally-bounded-Metric-Space :
  (l1 l2 l3 : Level) → UU (lsuc (l1 ⊔ l2 ⊔ l3))
inhabited-totally-bounded-Metric-Space l1 l2 l3 =
  type-subtype (is-inhabited-totally-bounded-prop-Metric-Space {l1} {l2} l3)

module _
  {l1 l2 l3 : Level}
  ((X , tbX , |X|) : inhabited-totally-bounded-Metric-Space l1 l2 l3)
  where

  metric-space-inhabited-totally-bounded-Metric-Space : Metric-Space l1 l2
  metric-space-inhabited-totally-bounded-Metric-Space = X

  type-inhabited-totally-bounded-Metric-Space : UU l1
  type-inhabited-totally-bounded-Metric-Space = type-Metric-Space X

  is-inhabited-inhabited-totally-bounded-Metric-Space :
    is-inhabited type-inhabited-totally-bounded-Metric-Space
  is-inhabited-inhabited-totally-bounded-Metric-Space = |X|

  is-totally-bounded-inhabited-totally-bounded-Metric-Space :
    is-totally-bounded-Metric-Space
      ( l3)
      ( metric-space-inhabited-totally-bounded-Metric-Space)
  is-totally-bounded-inhabited-totally-bounded-Metric-Space = tbX

  totally-bounded-space-inhabited-totally-bounded-Metric-Space :
    Totally-Bounded-Metric-Space l1 l2 l3
  totally-bounded-space-inhabited-totally-bounded-Metric-Space = (X , tbX)
```
