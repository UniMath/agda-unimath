# Functions between proper closed intervals of real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.maps-between-proper-closed-intervals-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.function-types
open import foundation.universe-levels

open import real-numbers.dedekind-real-numbers
open import real-numbers.proper-closed-intervals-real-numbers
```

</details>

## Idea

The type of
{{#concept "maps" Disambiguation="between proper closed intervals" Agda=map-proper-closed-interval-ℝ}}
between
[proper closed intervals](real-numbers.proper-closed-intervals-real-numbers.md)
of [real numbers](real-numbers.dedekind-real-numbers.md) `I` and `J` is the type
of [functions](foundation.function-types.md) `I → J`, i.e., the type of
[real maps](real-numbers.real-maps-proper-closed-intervals-real-numbers.md) on
`I` with values [in](foundation.subtypes.md) `J`.

## Definition

### Maps between proper closed intervals of real numbers

```agda
module _
  {l1 l2 l3 l4 : Level} (l l' : Level)
  (I : proper-closed-interval-ℝ l1 l2)
  (J : proper-closed-interval-ℝ l3 l4)
  where

  map-proper-closed-interval-ℝ :
    UU (lsuc l ⊔ lsuc l' ⊔ l1 ⊔ l2 ⊔ l3 ⊔ l4)
  map-proper-closed-interval-ℝ =
    type-proper-closed-interval-ℝ l I → type-proper-closed-interval-ℝ l' J
```

## Properties

### The identity map on a proper closed interval

```agda
module _
  {l1 l2 l3 l4 : Level} (l : Level)
  (I : proper-closed-interval-ℝ l1 l2)
  where

  id-proper-closed-interval-ℝ : map-proper-closed-interval-ℝ l l I I
  id-proper-closed-interval-ℝ = id
```

### Composition of maps between proper closed intervals

```agda
module _
  {l1 l2 l3 l4 l5 l6 l l' l'' : Level}
  {I : proper-closed-interval-ℝ l1 l2}
  {J : proper-closed-interval-ℝ l3 l4}
  {K : proper-closed-interval-ℝ l5 l6}
  (g : map-proper-closed-interval-ℝ l' l'' J K)
  (f : map-proper-closed-interval-ℝ l l' I J)
  where

  comp-map-proper-closed-interval-ℝ : map-proper-closed-interval-ℝ l l'' I K
  comp-map-proper-closed-interval-ℝ = g ∘ f
```
