# Inhabited, totally bounded subsets of the nonnegative real numbers

```agda
module real-numbers.inhabited-totally-bounded-subsets-nonnegative-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.images-subtypes
open import foundation.inhabited-subtypes
open import foundation.inhabited-types
open import foundation.subtypes
open import foundation.subtypes-of-subtypes
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import metric-spaces.inhabited-totally-bounded-subspaces-metric-spaces
open import metric-spaces.totally-bounded-subspaces-metric-spaces

open import real-numbers.inhabited-totally-bounded-subsets-real-numbers
open import real-numbers.metric-space-of-nonnegative-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.subsets-real-numbers
open import real-numbers.suprema-families-nonnegative-real-numbers
open import real-numbers.totally-bounded-subsets-real-numbers
```

</details>

## Idea

A [subset](foundation.subtypes.md) of the
[nonnegative real numbers](real-numbers.nonnegative-real-numbers.md) is
{{#concept "inhabited and totally bounded" Disambiguation="subset of the nonnegative-real numbers" Agda=inhabited-totally-bounded-subset-ℝ⁰⁺}}
if it is an
[inhabited, totally bounded subspace](metric-spaces.inhabited-totally-bounded-subspaces-metric-spaces.md)
of the
[metric space of nonnegative real numbers](real-numbers.metric-space-of-nonnegative-real-numbers.md).

## Definition

```agda
inhabited-totally-bounded-subset-ℝ⁰⁺ :
  (l1 l2 l3 : Level) → UU (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
inhabited-totally-bounded-subset-ℝ⁰⁺ l1 l2 l3 =
  inhabited-totally-bounded-subspace-Metric-Space l1 l3 (metric-space-ℝ⁰⁺ l2)

module _
  {l1 l2 l3 : Level} (S : inhabited-totally-bounded-subset-ℝ⁰⁺ l1 l2 l3)
  where

  subset-inhabited-totally-bounded-subset-ℝ⁰⁺ : subtype l1 (ℝ⁰⁺ l2)
  subset-inhabited-totally-bounded-subset-ℝ⁰⁺ =
    subset-inhabited-totally-bounded-subspace-Metric-Space
      ( metric-space-ℝ⁰⁺ l2)
      ( S)

  is-inhabited-subset-inhabited-totally-bounded-subset-ℝ⁰⁺ :
    is-inhabited-subtype subset-inhabited-totally-bounded-subset-ℝ⁰⁺
  is-inhabited-subset-inhabited-totally-bounded-subset-ℝ⁰⁺ = pr2 S
```

## Properties

### Inhabited, totally bounded subsets of ℝ⁰⁺ have suprema

```agda
module _
  {l1 l2 l3 : Level}
  (S@((subset-S , tb-S) , |S|) : inhabited-totally-bounded-subset-ℝ⁰⁺ l1 l2 l3)
  where

  subset-real-inhabited-totally-bounded-subset-ℝ⁰⁺ : subset-ℝ (l1 ⊔ l2) l2
  subset-real-inhabited-totally-bounded-subset-ℝ⁰⁺ =
    subtype-subtype-of-subtype is-nonnegative-prop-ℝ subset-S

  abstract
    is-inhabited-subset-real-inhabited-totally-bounded-subset-ℝ :
      is-inhabited-subtype
        ( subset-real-inhabited-totally-bounded-subset-ℝ⁰⁺)
    is-inhabited-subset-real-inhabited-totally-bounded-subset-ℝ =
      map-is-inhabited map-associative-Σ |S|

    is-totally-bounded-subset-real-inhabited-totally-bounded-subset-ℝ :
      is-totally-bounded-subset-ℝ
        ( l1 ⊔ lsuc l2 ⊔ l3)
        ( subset-real-inhabited-totally-bounded-subset-ℝ⁰⁺)
    is-totally-bounded-subset-real-inhabited-totally-bounded-subset-ℝ =
      is-totally-bounded-subspace-of-subspace-Metric-Space
        ( metric-space-ℝ l2)
        ( is-nonnegative-prop-ℝ)
        ( subset-S)
        ( tb-S)

  inhabited-totally-bounded-subset-real-inhabited-totally-bounded-subset-ℝ⁰⁺ :
    inhabited-totally-bounded-subset-ℝ (l1 ⊔ l2) l2 (l1 ⊔ lsuc l2 ⊔ l3)
  inhabited-totally-bounded-subset-real-inhabited-totally-bounded-subset-ℝ⁰⁺ =
    ( ( subset-real-inhabited-totally-bounded-subset-ℝ⁰⁺ ,
        is-totally-bounded-subset-real-inhabited-totally-bounded-subset-ℝ) ,
      is-inhabited-subset-real-inhabited-totally-bounded-subset-ℝ)

  abstract
    has-supremum-inhabited-totally-bounded-subset-ℝ⁰⁺ :
      has-supremum-subset-ℝ⁰⁺
        ( l2)
        ( subset-inhabited-totally-bounded-subset-ℝ⁰⁺ S)
    has-supremum-inhabited-totally-bounded-subset-ℝ⁰⁺ =
      has-nonnegative-supremum-has-supremum-subset-ℝ⁰⁺
        ( subset-inhabited-totally-bounded-subset-ℝ⁰⁺ S)
        ( has-supremum-inhabited-totally-bounded-subset-ℝ
          ( inhabited-totally-bounded-subset-real-inhabited-totally-bounded-subset-ℝ⁰⁺))

  sup-inhabited-totally-bounded-subset-ℝ⁰⁺ : ℝ⁰⁺ l2
  sup-inhabited-totally-bounded-subset-ℝ⁰⁺ =
    pr1 has-supremum-inhabited-totally-bounded-subset-ℝ⁰⁺

  is-supremum-sup-inhabited-totally-bounded-subset-ℝ⁰⁺ :
    is-supremum-subset-ℝ⁰⁺
      ( subset-inhabited-totally-bounded-subset-ℝ⁰⁺ S)
      ( sup-inhabited-totally-bounded-subset-ℝ⁰⁺)
  is-supremum-sup-inhabited-totally-bounded-subset-ℝ⁰⁺ =
    pr2 has-supremum-inhabited-totally-bounded-subset-ℝ⁰⁺
```
