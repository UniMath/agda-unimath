# Accumulation points of subsets of the real numbers

```agda
module real-numbers.accumulation-points-subsets-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import lists.sequences

open import metric-spaces.accumulation-points-subsets-located-metric-spaces

open import real-numbers.apartness-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.limits-sequences-real-numbers
open import real-numbers.located-metric-space-of-real-numbers
open import real-numbers.subsets-real-numbers
```

</details>

## Idea

An
{{#concept "accumulation point" Disambiguation="of a subset of ℝ" Agda=accumulation-point-subset-ℝ}}
of a [subset](real-numbers.subsets-real-numbers.md) `S` of the
[real numbers](real-numbers.dedekind-real-numbers.md) is an
[accumulation point](metric-spaces.accumulation-points-located-metric-spaces.md)
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

  is-sequential-accumulation-point-subset-ℝ : ℝ l2 → UU (l1 ⊔ lsuc l2)
  is-sequential-accumulation-point-subset-ℝ =
    is-sequential-accumulation-point-subset-Located-Metric-Space
      ( located-metric-space-ℝ l2)
      ( S)

  is-sequential-accumulation-point-is-accumulation-point-subset-ℝ :
    (x : ℝ l2) → is-accumulation-point-subset-ℝ x →
    is-sequential-accumulation-point-subset-ℝ x
  is-sequential-accumulation-point-is-accumulation-point-subset-ℝ =
    is-sequential-accumulation-point-is-accumulation-point-subset-Located-Metric-Space
      ( located-metric-space-ℝ l2)
      ( S)

  is-sequence-approaching-point-prop-subset-ℝ :
    ℝ l2 → subtype l2 (sequence (type-subtype S))
  is-sequence-approaching-point-prop-subset-ℝ =
    is-sequence-approaching-point-prop-subset-Located-Metric-Space
      ( located-metric-space-ℝ l2)
      ( S)

  is-sequence-approaching-point-subset-ℝ :
    ℝ l2 → sequence (type-subtype S) → UU l2
  is-sequence-approaching-point-subset-ℝ x =
    is-in-subtype (is-sequence-approaching-point-prop-subset-ℝ x)

  sequence-approaching-point-subset-ℝ : ℝ l2 → UU (l1 ⊔ lsuc l2)
  sequence-approaching-point-subset-ℝ x =
    type-subtype (is-sequence-approaching-point-prop-subset-ℝ x)

  accumulation-point-subset-ℝ : UU (l1 ⊔ lsuc l2)
  accumulation-point-subset-ℝ = type-subtype is-accumulation-point-prop-subset-ℝ
```

## Properties

### Properties of a sequence approaching a point

```agda
module _
  {l1 l2 : Level}
  (S : subset-ℝ l1 l2)
  (x : ℝ l2)
  (y : sequence-approaching-point-subset-ℝ S x)
  where

  map-sequence-approaching-point-subset-ℝ : sequence (type-subtype S)
  map-sequence-approaching-point-subset-ℝ = pr1 y

  real-sequence-approaching-point-subset-ℝ : sequence (ℝ l2)
  real-sequence-approaching-point-subset-ℝ = pr1 ∘ pr1 y

  abstract
    apart-sequence-approaching-point-subset-ℝ :
      (n : ℕ) → apart-ℝ (real-sequence-approaching-point-subset-ℝ n) x
    apart-sequence-approaching-point-subset-ℝ n =
      apart-apart-located-metric-space-ℝ _ _ (pr1 (pr2 y) n)

    is-limit-sequence-approaching-point-subset-ℝ :
      is-limit-sequence-ℝ real-sequence-approaching-point-subset-ℝ x
    is-limit-sequence-approaching-point-subset-ℝ =
      pr2 (pr2 y)
```
