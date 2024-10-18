# Maps between large globular types

```agda
{-# OPTIONS --guardedness #-}

module structured-types.large-globular-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.universe-levels

open import structured-types.globular-maps
open import structured-types.globular-types
open import structured-types.large-globular-types
```

</details>

## Idea

A {{#concept "large globular map" Agda=large-globular-map}}
`f` between [large globular types](structured-types.large-globular-types.md) `A`
and `B` consists of a map `F₀` of $0$-cells, and for every pair of $n$-cells `x` and `y`,
a map of $(n+1)$-cells

```text
  Fₙ₊₁ : (𝑛+1)-Cell A x y → (𝑛+1)-Cell B (Fₙ x) (Fₙ y).
```

## Definitions

### Maps between large globular types

```agda
record
  large-globular-map
  {α1 α2 : Level → Level} {β1 β2 : Level → Level → Level} (δ : Level → Level)
  (A : Large-Globular-Type α1 β1) (B : Large-Globular-Type α2 β2) : UUω
  where

  field
    0-cell-large-globular-map :
      {l : Level} →
      0-cell-Large-Globular-Type A l → 0-cell-Large-Globular-Type B (δ l)

  field
    1-cell-globular-map-large-globular-map :
      {l1 l2 : Level}
      {x : 0-cell-Large-Globular-Type A l1}
      {y : 0-cell-Large-Globular-Type A l2} →
      globular-map
        ( 1-cell-globular-type-Large-Globular-Type A x y)
        ( 1-cell-globular-type-Large-Globular-Type B
          ( 0-cell-large-globular-map x)
          ( 0-cell-large-globular-map y))

  1-cell-large-globular-map :
    {l1 l2 : Level}
    {x : 0-cell-Large-Globular-Type A l1}
    {y : 0-cell-Large-Globular-Type A l2} →
    1-cell-Large-Globular-Type A x y →
    1-cell-Large-Globular-Type B
      ( 0-cell-large-globular-map x)
      ( 0-cell-large-globular-map y)
  1-cell-large-globular-map =
    0-cell-globular-map 1-cell-globular-map-large-globular-map

  2-cell-globular-map-large-globular-map :
    {l1 l2 : Level}
    {x : 0-cell-Large-Globular-Type A l1}
    {y : 0-cell-Large-Globular-Type A l2}
    (f g : 1-cell-Large-Globular-Type A x y) →
    globular-map
      ( 2-cell-globular-type-Large-Globular-Type A f g)
      ( 2-cell-globular-type-Large-Globular-Type B
        ( 1-cell-large-globular-map f)
        ( 1-cell-large-globular-map g))
  2-cell-globular-map-large-globular-map f g =
    1-cell-globular-map-globular-map
      1-cell-globular-map-large-globular-map

  2-cell-large-globular-map :
    {l1 l2 : Level}
    {x : 0-cell-Large-Globular-Type A l1}
    {y : 0-cell-Large-Globular-Type A l2} →
    {f g : 1-cell-Large-Globular-Type A x y} →
    2-cell-Large-Globular-Type A f g →
    2-cell-Large-Globular-Type B
      ( 1-cell-large-globular-map f)
      ( 1-cell-large-globular-map g)
  2-cell-large-globular-map =
    1-cell-globular-map 1-cell-globular-map-large-globular-map

  3-cell-globular-map-large-globular-map :
    {l1 l2 : Level}
    {x : 0-cell-Large-Globular-Type A l1}
    {y : 0-cell-Large-Globular-Type A l2}
    {f g : 1-cell-Large-Globular-Type A x y}
    (s t : 2-cell-Large-Globular-Type A f g) →
    globular-map
      ( 3-cell-globular-type-Large-Globular-Type A s t)
      ( 3-cell-globular-type-Large-Globular-Type B
        ( 2-cell-large-globular-map s)
        ( 2-cell-large-globular-map t))
  3-cell-globular-map-large-globular-map =
    2-cell-globular-map-globular-map
      1-cell-globular-map-large-globular-map

  3-cell-large-globular-map :
    {l1 l2 : Level}
    {x : 0-cell-Large-Globular-Type A l1}
    {y : 0-cell-Large-Globular-Type A l2} →
    {f g : 1-cell-Large-Globular-Type A x y} →
    {H K : 2-cell-Large-Globular-Type A f g} →
    3-cell-Large-Globular-Type A H K →
    3-cell-Large-Globular-Type B
      ( 2-cell-large-globular-map H)
      ( 2-cell-large-globular-map K)
  3-cell-large-globular-map =
    2-cell-globular-map 1-cell-globular-map-large-globular-map

open large-globular-map public
```

### Large identity globular maps

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (A : Large-Globular-Type α β)
  where

  id-large-globular-map : large-globular-map id A A
  0-cell-large-globular-map id-large-globular-map =
    id
  1-cell-globular-map-large-globular-map id-large-globular-map =
    id-globular-map (1-cell-globular-type-Large-Globular-Type A _ _)
```

### Composition of large globular maps

```agda
module _
  {α1 α2 α3 δ1 δ2 : Level → Level} {β1 β2 β3 : Level → Level → Level}
  {A : Large-Globular-Type α1 β1}
  {B : Large-Globular-Type α2 β2}
  {C : Large-Globular-Type α3 β3}
  where

  comp-large-globular-map :
    (g : large-globular-map δ2 B C) (f : large-globular-map δ1 A B) →
    large-globular-map (δ2 ∘ δ1) A C
  0-cell-large-globular-map (comp-large-globular-map g f) =
    0-cell-large-globular-map g ∘ 0-cell-large-globular-map f
  1-cell-globular-map-large-globular-map (comp-large-globular-map g f) =
    comp-globular-map
      ( 1-cell-globular-map-large-globular-map g)
      ( 1-cell-globular-map-large-globular-map f)
```
