# Maps between large globular types

```agda
{-# OPTIONS --guardedness #-}

module structured-types.maps-large-globular-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import structured-types.globular-types
open import structured-types.large-globular-types
open import structured-types.maps-globular-types
```

</details>

## Idea

A
{{#concept "map" Disambiguation="large globular types" Agda=map-Large-Globular-Type}}
`f` between [large globular types](structured-types.large-globular-types.md) `A`
and `B` is a map `F₀` of $0$-cells, and for every pair of $n$-cells `x` and `y`,
a map of $(n+1)$-cells

```text
  Fₙ₊₁ : (𝑛+1)-Cell A x y → (𝑛+1)-Cell B (Fₙ x) (Fₙ y).
```

## Definitions

### Maps between large globular types

```agda
record
  map-Large-Globular-Type
  {α1 α2 : Level → Level} {β1 β2 : Level → Level → Level} (δ : Level → Level)
  (A : Large-Globular-Type α1 β1) (B : Large-Globular-Type α2 β2) : UUω
  where
  field
    0-cell-map-Large-Globular-Type :
      {l : Level} →
      0-cell-Large-Globular-Type A l → 0-cell-Large-Globular-Type B (δ l)

    globular-type-1-cell-map-Large-Globular-Type :
      {l1 l2 : Level}
      {x : 0-cell-Large-Globular-Type A l1}
      {y : 0-cell-Large-Globular-Type A l2} →
      map-Globular-Type
        ( globular-type-1-cell-Large-Globular-Type A x y)
        ( globular-type-1-cell-Large-Globular-Type B
          ( 0-cell-map-Large-Globular-Type x)
          ( 0-cell-map-Large-Globular-Type y))

open map-Large-Globular-Type public

module _
  {α1 α2 : Level → Level} {β1 β2 : Level → Level → Level} {δ : Level → Level}
  {A : Large-Globular-Type α1 β1} {B : Large-Globular-Type α2 β2}
  (F : map-Large-Globular-Type δ A B)
  where

  1-cell-map-Large-Globular-Type :
    {l1 l2 : Level}
    {x : 0-cell-Large-Globular-Type A l1}
    {y : 0-cell-Large-Globular-Type A l2} →
    1-cell-Large-Globular-Type A x y →
    1-cell-Large-Globular-Type B
      ( 0-cell-map-Large-Globular-Type F x)
      ( 0-cell-map-Large-Globular-Type F y)
  1-cell-map-Large-Globular-Type =
    0-cell-map-Globular-Type (globular-type-1-cell-map-Large-Globular-Type F)

module _
  {α1 α2 : Level → Level} {β1 β2 : Level → Level → Level} {δ : Level → Level}
  {A : Large-Globular-Type α1 β1} {B : Large-Globular-Type α2 β2}
  (F : map-Large-Globular-Type δ A B)
  where

  2-cell-map-Large-Globular-Type :
    {l1 l2 : Level}
    {x : 0-cell-Large-Globular-Type A l1}
    {y : 0-cell-Large-Globular-Type A l2} →
    {f g : 1-cell-Large-Globular-Type A x y} →
    2-cell-Large-Globular-Type A f g →
    2-cell-Large-Globular-Type B
      ( 1-cell-map-Large-Globular-Type F f)
      ( 1-cell-map-Large-Globular-Type F g)
  2-cell-map-Large-Globular-Type =
    1-cell-map-Globular-Type (globular-type-1-cell-map-Large-Globular-Type F)

module _
  {α1 α2 : Level → Level} {β1 β2 : Level → Level → Level} {δ : Level → Level}
  {A : Large-Globular-Type α1 β1} {B : Large-Globular-Type α2 β2}
  (F : map-Large-Globular-Type δ A B)
  where

  3-cell-map-Large-Globular-Type :
    {l1 l2 : Level}
    {x : 0-cell-Large-Globular-Type A l1}
    {y : 0-cell-Large-Globular-Type A l2} →
    {f g : 1-cell-Large-Globular-Type A x y} →
    {H K : 2-cell-Large-Globular-Type A f g} →
    3-cell-Large-Globular-Type A H K →
    3-cell-Large-Globular-Type B
      ( 2-cell-map-Large-Globular-Type F H)
      ( 2-cell-map-Large-Globular-Type F K)
  3-cell-map-Large-Globular-Type =
    2-cell-map-Globular-Type (globular-type-1-cell-map-Large-Globular-Type F)
```
