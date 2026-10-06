# Real functions on proper closed intervals of real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.real-maps-proper-closed-intervals-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import real-numbers.dedekind-real-numbers
open import real-numbers.proper-closed-intervals-real-numbers
```

</details>

## Idea

The type of
{{#concept "real functions" Disambiguation="on a proper closed interval" Agda=real-map-proper-closed-interval-ℝ}}
on a
[proper closed interval](real-numbers.proper-closed-intervals-real-numbers.md)
of [real numbers](real-numbers.dedekind-real-numbers.md) `[a, b]`, is the type
of maps `[a, b] → ℝ`.

## Definition

### The type of real maps on a proper closed interval of real numbers

```agda
real-map-proper-closed-interval-ℝ :
  (l1 l2 : Level) {l3 l4 : Level} ([a,b] : proper-closed-interval-ℝ l3 l4) →
  UU (lsuc l1 ⊔ lsuc l2 ⊔ l3 ⊔ l4)
real-map-proper-closed-interval-ℝ l1 l2 [a,b] =
  type-proper-closed-interval-ℝ l1 [a,b] → ℝ l2
```

## Properties

### A real endomap restricts to any proper closed interval

```agda
restrict-real-endomap-real-map-proper-closed-interval-ℝ :
  {l1 l2 l3 l4 : Level} →
  ([a,b] : proper-closed-interval-ℝ l3 l4) →
  (f : ℝ l1 → ℝ l2) →
  real-map-proper-closed-interval-ℝ l1 l2 [a,b]
restrict-real-endomap-real-map-proper-closed-interval-ℝ I f (x , x∈I) = f x
```

### Clamping a real map on a proper closed interval

```agda
module _
  {l1 l2 l3 l4 : Level}
  ([a,b] : proper-closed-interval-ℝ l3 l4)
  (f : real-map-proper-closed-interval-ℝ (l1 ⊔ l3 ⊔ l4) l2 [a,b])
  where

  clamp-real-map-proper-closed-interval-ℝ : ℝ l1 → ℝ l2
  clamp-real-map-proper-closed-interval-ℝ x =
    f (clamp-proper-closed-interval-ℝ [a,b] x)
```
