# Accumulation points of subsets of the real numbers

```agda
module real-numbers.accumulation-points-subsets-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import lists.sequences

open import metric-spaces.accumulation-points-subsets-located-metric-spaces

open import real-numbers.dedekind-real-numbers
open import real-numbers.located-metric-space-of-real-numbers
open import real-numbers.subsets-real-numbers
```

</details>

## Idea

An
{{#concept "accumulation point" Disambiguation="of a subset of ℝ" Agda=accumulation-point-subset-ℝ}}
of a [subset](real-numbers.subsets-real-numbers.md) `S` of the
[real numbers](real-numbers.dedekind-real-numbers.md) is an
[accumulation point](metric-spaces.accumulation-points-subsets-located-metric-spaces.md)
of `S` in the
[located metric space of the real numbers](real-numbers.located-metric-space-of-real-numbers.md).

### Accumulation points of subsets of ℝ

```agda
module _
  {l1 l2 : Level} (S : subset-ℝ l1 l2)
  where

  is-accumulation-point-prop-subset-ℝ : subset-ℝ (l1 ⊔ lsuc l2) l2
  is-accumulation-point-prop-subset-ℝ =
    is-accumulation-point-prop-subset-Located-Metric-Space
      ( located-metric-space-ℝ l2)
      ( S)

  is-accumulation-point-subset-ℝ : ℝ l2 → UU (l1 ⊔ lsuc l2)
  is-accumulation-point-subset-ℝ x =
    type-Prop (is-accumulation-point-prop-subset-ℝ x)

  accumulation-point-subset-ℝ : UU (l1 ⊔ lsuc l2)
  accumulation-point-subset-ℝ = type-subtype is-accumulation-point-prop-subset-ℝ
```
