# Compact metric spaces

```agda
module metric-spaces.compact-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.conjunction
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import metric-spaces.complete-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.totally-bounded-metric-spaces
```

</details>

## Idea

A [metric space](metric-spaces.metric-spaces.md) is
{{#concept "compact" WDID=Q381892 WD="compact space" Agda=is-compact-Metric-Space}}
if it is [totally bounded](metric-spaces.totally-bounded-metric-spaces.md) and
[complete](metric-spaces.complete-metric-spaces.md).

## Definition

```agda
module _
  {l1 l2 : Level} (l3 : Level) (X : Metric-Space l1 l2)
  where

  is-compact-prop-Metric-Space : Prop (l1 ⊔ l2 ⊔ lsuc l3)
  is-compact-prop-Metric-Space =
    is-totally-bounded-prop-Metric-Space l3 X ∧ is-complete-prop-Metric-Space X

  is-compact-Metric-Space : UU (l1 ⊔ l2 ⊔ lsuc l3)
  is-compact-Metric-Space = type-Prop is-compact-prop-Metric-Space

Compact-Metric-Space : (l1 l2 l3 : Level) → UU (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
Compact-Metric-Space l1 l2 l3 =
  type-subtype (is-compact-prop-Metric-Space {l1} {l2} l3)
```
