# Sequences in metric abelian groups

```agda
module analysis.sequences-metric-abelian-groups where
```

<details><summary>Imports</summary>

```agda
open import analysis.metric-abelian-groups

open import foundation.universe-levels

open import lists.sequences
```

</details>

## Idea

A [sequence](lists.sequences.md) in a
[metric abelian group](analysis.metric-abelian-groups.md) inherits the
operations of the group.

## Definition

```agda
sequence-type-Metric-Ab : {l1 l2 : Level} → Metric-Ab l1 l2 → UU l1
sequence-type-Metric-Ab G = sequence (type-Metric-Ab G)

add-sequence-type-Metric-Ab :
  {l1 l2 : Level} (G : Metric-Ab l1 l2) →
  sequence-type-Metric-Ab G → sequence-type-Metric-Ab G →
  sequence-type-Metric-Ab G
add-sequence-type-Metric-Ab G = binary-map-sequence (add-Metric-Ab G)

neg-sequence-type-Metric-Ab :
  {l1 l2 : Level} (G : Metric-Ab l1 l2) →
  sequence-type-Metric-Ab G → sequence-type-Metric-Ab G
neg-sequence-type-Metric-Ab G = map-sequence (neg-Metric-Ab G)
```
