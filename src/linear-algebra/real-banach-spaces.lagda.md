# Real Banach spaces

```agda
{-# OPTIONS --lossy-unification #-}

module linear-algebra.real-banach-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import linear-algebra.normed-real-vector-spaces

open import metric-spaces.complete-metric-spaces
```

</details>

## Idea

A real
{{#concept "Banach space" WDID=Q194397 WD="Banach space" Disambiguation="over the real numbers" Agda=ℝ-Banach-Space}}
is a [normed](linear-algebra.normed-real-vector-spaces.md)
[real vector space](linear-algebra.real-vector-spaces.md) such that the
[metric space](metric-spaces.metric-spaces.md) induced by the norm is
[complete](metric-spaces.complete-metric-spaces.md).

## Definition

```agda
is-banach-prop-Normed-ℝ-Vector-Space :
  {l1 l2 : Level} (V : Normed-ℝ-Vector-Space l1 l2) → Prop (l1 ⊔ l2)
is-banach-prop-Normed-ℝ-Vector-Space V =
  is-complete-prop-Metric-Space (metric-space-Normed-ℝ-Vector-Space V)

is-banach-Normed-ℝ-Vector-Space :
  {l1 l2 : Level} (V : Normed-ℝ-Vector-Space l1 l2) → UU (l1 ⊔ l2)
is-banach-Normed-ℝ-Vector-Space V =
  type-Prop (is-banach-prop-Normed-ℝ-Vector-Space V)

ℝ-Banach-Space : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
ℝ-Banach-Space l1 l2 =
  type-subtype (is-banach-prop-Normed-ℝ-Vector-Space {l1} {l2})
```
