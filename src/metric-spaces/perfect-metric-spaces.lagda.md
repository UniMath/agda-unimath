# Perfect metric spaces

```agda
module metric-spaces.perfect-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.full-subtypes
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import metric-spaces.accumulation-points-subsets-located-metric-spaces
open import metric-spaces.located-metric-spaces
```

</details>

## Idea

A [located metric space](metric-spaces.located-metric-spaces.md) is
{{#concept "perfect" Disambiguation="located metric space" Agda=is-perfect-Located-Metric-Space}}
if every one of its points is an
[accumulation point](metric-spaces.accumulation-points-subsets-located-metric-spaces.md).

## Definition

```agda
is-perfect-prop-Located-Metric-Space :
  {l1 l2 : Level} → subtype (l1 ⊔ l2) (Located-Metric-Space l1 l2)
is-perfect-prop-Located-Metric-Space X =
  is-full-subtype-Prop
    ( is-accumulation-point-prop-subset-Located-Metric-Space
      ( X)
      ( full-subtype lzero (type-Located-Metric-Space X)))

is-perfect-Located-Metric-Space :
  {l1 l2 : Level} → Located-Metric-Space l1 l2 → UU (l1 ⊔ l2)
is-perfect-Located-Metric-Space =
  is-in-subtype is-perfect-prop-Located-Metric-Space

Perfect-Metric-Space : (l1 l2 : Level) → UU (lsuc (l1 ⊔ l2))
Perfect-Metric-Space l1 l2 =
  type-subtype (is-perfect-prop-Located-Metric-Space {l1} {l2})
```

## External links

- [Perfect set](https://en.wikipedia.org/wiki/Perfect_set) on Wikipedia
