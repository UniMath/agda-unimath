# Maps between globular types

```agda
{-# OPTIONS --guardedness #-}

module structured-types.maps-globular-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.universe-levels

open import structured-types.globular-types
```

</details>

## Idea

A {{#concept "map" Disambiguation="globular types" Agda=map-Globular-Type}} `f`
between [globular types](structured-types.globular-types.md) `A` and `B` is a
map `F₀` of $0$-cells, and for every pair of $n$-cells `x` and `y`, a map of
$(n+1)$-cells

```text
  Fₙ₊₁ : (𝑛+1)-Cell A x y → (𝑛+1)-Cell B (Fₙ x) (Fₙ y).
```

## Definitions

### Maps between globular types

```agda
record
  map-Globular-Type
  {l1 l2 l3 l4 : Level} (A : Globular-Type l1 l2) (B : Globular-Type l3 l4)
  : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  where
  coinductive
  field
    0-cell-map-Globular-Type :
      0-cell-Globular-Type A → 0-cell-Globular-Type B

    globular-type-1-cell-map-Globular-Type :
      {x y : 0-cell-Globular-Type A} →
      map-Globular-Type
        ( globular-type-1-cell-Globular-Type A x y)
        ( globular-type-1-cell-Globular-Type B
          ( 0-cell-map-Globular-Type x)
          ( 0-cell-map-Globular-Type y))

open map-Globular-Type public

module _
  {l1 l2 l3 l4 : Level}
  {A : Globular-Type l1 l2} {B : Globular-Type l3 l4}
  (F : map-Globular-Type A B)
  where

  1-cell-map-Globular-Type :
    {x y : 0-cell-Globular-Type A} →
    1-cell-Globular-Type A x y →
    1-cell-Globular-Type B
      ( 0-cell-map-Globular-Type F x)
      ( 0-cell-map-Globular-Type F y)
  1-cell-map-Globular-Type =
    0-cell-map-Globular-Type (globular-type-1-cell-map-Globular-Type F)

module _
  {l1 l2 l3 l4 : Level}
  {A : Globular-Type l1 l2} {B : Globular-Type l3 l4}
  (F : map-Globular-Type A B)
  where

  2-cell-map-Globular-Type :
    {x y : 0-cell-Globular-Type A}
    {f g : 1-cell-Globular-Type A x y} →
    2-cell-Globular-Type A f g →
    2-cell-Globular-Type B
      ( 1-cell-map-Globular-Type F f)
      ( 1-cell-map-Globular-Type F g)
  2-cell-map-Globular-Type =
    1-cell-map-Globular-Type (globular-type-1-cell-map-Globular-Type F)

module _
  {l1 l2 l3 l4 : Level}
  {A : Globular-Type l1 l2} {B : Globular-Type l3 l4}
  (F : map-Globular-Type A B)
  where

  3-cell-map-Globular-Type :
    {x y : 0-cell-Globular-Type A}
    {f g : 1-cell-Globular-Type A x y} →
    {H K : 2-cell-Globular-Type A f g} →
    3-cell-Globular-Type A H K →
    3-cell-Globular-Type B
      ( 2-cell-map-Globular-Type F H)
      ( 2-cell-map-Globular-Type F K)
  3-cell-map-Globular-Type =
    2-cell-map-Globular-Type (globular-type-1-cell-map-Globular-Type F)
```

### The identity map on a globular type

```agda
id-map-Globular-Type :
  {l1 l2 : Level} (A : Globular-Type l1 l2) → map-Globular-Type A A
id-map-Globular-Type A =
  λ where
  .0-cell-map-Globular-Type → id
  .globular-type-1-cell-map-Globular-Type {x} {y} →
    id-map-Globular-Type (globular-type-1-cell-Globular-Type A x y)
```

### Composition of maps of globular types

```agda
comp-map-Globular-Type :
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : Globular-Type l1 l2}
  {B : Globular-Type l3 l4}
  {C : Globular-Type l5 l6} →
  map-Globular-Type B C → map-Globular-Type A B → map-Globular-Type A C
comp-map-Globular-Type g f =
  λ where
  .0-cell-map-Globular-Type →
    0-cell-map-Globular-Type g ∘ 0-cell-map-Globular-Type f
  .globular-type-1-cell-map-Globular-Type →
    comp-map-Globular-Type
      ( globular-type-1-cell-map-Globular-Type g)
      ( globular-type-1-cell-map-Globular-Type f)
```
