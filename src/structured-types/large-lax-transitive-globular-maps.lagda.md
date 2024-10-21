# Large lax transitive globular maps

```agda
{-# OPTIONS --guardedness #-}

module structured-types.large-lax-transitive-globular-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.function-types
open import foundation.universe-levels

open import structured-types.large-globular-maps
open import structured-types.large-transitive-globular-types
open import structured-types.lax-transitive-globular-maps
open import structured-types.transitive-globular-types
```

</details>

## Idea

A
{{#concept "large lax transitive globular map" Agda=large-lax-transitive-globular-map}}
between two
[large transitive globular types](structured-types.large-transitive-globular-types.md)
`G` and `H` is a [large globular map](structured-types.large-globular-maps.md)
`f : G → H` equipped with a family of 2-cells

```text
  H₂ (f₁ (q ∘G p)) (f₁ q ∘H f₁ p)
```

from the image of the composite of two 1-cells `q` and `p` in `G` to the
composite of `f₁ q` and `f₁ p` in `H`, such that the globular map
`f' : G' x y → H' (f₀ x) (f₀ y)` is again lax transitive.

### Lack of identity large lax transitive globular maps

Note that the large lax transitive globular maps lack an identity morphism. For
an identity morphism to exist on a transitive globular type `G`, there should be
a `2`-cell from `q ∘G p` to `q ∘G p` for every composable pair of `1`-cells `q`
and `p`. However, since the large transitive globular type `G` is not assumed to
be [reflexive](structured-types.large-reflexive-globular-types.md), it might
lack such instances of the reflexivity cells.

## Definitions

### The predicate of lax preserving transitivity

```agda
record
  is-lax-transitive-large-globular-map
    {α1 α2 : Level → Level} {β1 β2 : Level → Level → Level} {γ : Level → Level}
    (G : Large-Transitive-Globular-Type α1 β1)
    (H : Large-Transitive-Globular-Type α2 β2)
    (f : large-globular-map-Large-Transitive-Globular-Type γ G H) : UUω
  where
  coinductive

  field
    preserves-comp-1-cell-is-lax-transitive-large-globular-map :
      {l1 l2 l3 : Level}
      {x : 0-cell-Large-Transitive-Globular-Type G l1}
      {y : 0-cell-Large-Transitive-Globular-Type G l2}
      {z : 0-cell-Large-Transitive-Globular-Type G l3} →
      (q : 1-cell-Large-Transitive-Globular-Type G y z)
      (p : 1-cell-Large-Transitive-Globular-Type G x y) →
      2-cell-Large-Transitive-Globular-Type H
        ( comp-1-cell-Large-Transitive-Globular-Type H
          ( 1-cell-large-globular-map f q)
          ( 1-cell-large-globular-map f p))
        ( 1-cell-large-globular-map f
          ( comp-1-cell-Large-Transitive-Globular-Type G q p))

  field
    is-lax-transitive-1-cell-globular-map-is-lax-transitive-large-globular-map :
      {l1 l2 : Level}
      {x : 0-cell-Large-Transitive-Globular-Type G l1}
      {y : 0-cell-Large-Transitive-Globular-Type G l2} →
      is-lax-transitive-globular-map
        ( 1-cell-transitive-globular-type-Large-Transitive-Globular-Type G x y)
        ( 1-cell-transitive-globular-type-Large-Transitive-Globular-Type H _ _)
        ( 1-cell-globular-map-large-globular-map f)

open is-lax-transitive-large-globular-map public
```

### Lax transitive globular maps

```agda
record
  large-lax-transitive-globular-map
    {α1 α2 : Level → Level} {β1 β2 : Level → Level → Level} (γ : Level → Level)
    (G : Large-Transitive-Globular-Type α1 β1)
    (H : Large-Transitive-Globular-Type α2 β2) : UUω
  where

  field
    large-globular-map-large-lax-transitive-globular-map :
      large-globular-map-Large-Transitive-Globular-Type γ G H

  0-cell-large-lax-transitive-globular-map :
    {l1 : Level} →
    0-cell-Large-Transitive-Globular-Type G l1 →
    0-cell-Large-Transitive-Globular-Type H (γ l1)
  0-cell-large-lax-transitive-globular-map =
    0-cell-large-globular-map
      large-globular-map-large-lax-transitive-globular-map

  1-cell-large-lax-transitive-globular-map :
    {l1 l2 : Level}
    {x : 0-cell-Large-Transitive-Globular-Type G l1}
    {y : 0-cell-Large-Transitive-Globular-Type G l2} →
    1-cell-Large-Transitive-Globular-Type G x y →
    1-cell-Large-Transitive-Globular-Type H
      ( 0-cell-large-lax-transitive-globular-map x)
      ( 0-cell-large-lax-transitive-globular-map y)
  1-cell-large-lax-transitive-globular-map =
    1-cell-large-globular-map
      large-globular-map-large-lax-transitive-globular-map

  1-cell-globular-map-large-lax-transitive-globular-map :
    {l1 l2 : Level}
    {x : 0-cell-Large-Transitive-Globular-Type G l1}
    {y : 0-cell-Large-Transitive-Globular-Type G l2} →
    globular-map-Transitive-Globular-Type
      ( 1-cell-transitive-globular-type-Large-Transitive-Globular-Type G x y)
      ( 1-cell-transitive-globular-type-Large-Transitive-Globular-Type H
        ( 0-cell-large-lax-transitive-globular-map x)
        ( 0-cell-large-lax-transitive-globular-map y))
  1-cell-globular-map-large-lax-transitive-globular-map =
    1-cell-globular-map-large-globular-map
      large-globular-map-large-lax-transitive-globular-map

  2-cell-large-lax-transitive-globular-map :
    {l1 l2 : Level}
    {x : 0-cell-Large-Transitive-Globular-Type G l1}
    {y : 0-cell-Large-Transitive-Globular-Type G l2} →
    {f g : 1-cell-Large-Transitive-Globular-Type G x y} →
    2-cell-Large-Transitive-Globular-Type G f g →
    2-cell-Large-Transitive-Globular-Type H
      ( 1-cell-large-lax-transitive-globular-map f)
      ( 1-cell-large-lax-transitive-globular-map g)
  2-cell-large-lax-transitive-globular-map =
    2-cell-large-globular-map
      large-globular-map-large-lax-transitive-globular-map

  2-cell-globular-map-large-lax-transitive-globular-map :
    {l1 l2 : Level}
    {x : 0-cell-Large-Transitive-Globular-Type G l1}
    {y : 0-cell-Large-Transitive-Globular-Type G l2} →
    {f g : 1-cell-Large-Transitive-Globular-Type G x y} →
    globular-map-Transitive-Globular-Type
      ( 2-cell-transitive-globular-type-Large-Transitive-Globular-Type G f g)
      ( 2-cell-transitive-globular-type-Large-Transitive-Globular-Type H
        ( 1-cell-large-lax-transitive-globular-map f)
        ( 1-cell-large-lax-transitive-globular-map g))
  2-cell-globular-map-large-lax-transitive-globular-map =
    2-cell-globular-map-large-globular-map
      ( large-globular-map-large-lax-transitive-globular-map)
      ( _)
      ( _)

  field
    is-lax-transitive-large-lax-transitive-globular-map :
      is-lax-transitive-large-globular-map G H
        large-globular-map-large-lax-transitive-globular-map

  preserves-comp-1-cell-large-lax-transitive-globular-map :
    {l1 l2 l3 : Level}
    {x : 0-cell-Large-Transitive-Globular-Type G l1}
    {y : 0-cell-Large-Transitive-Globular-Type G l2}
    {z : 0-cell-Large-Transitive-Globular-Type G l3}
    (q : 1-cell-Large-Transitive-Globular-Type G y z)
    (p : 1-cell-Large-Transitive-Globular-Type G x y) →
    2-cell-Large-Transitive-Globular-Type H
      ( comp-1-cell-Large-Transitive-Globular-Type H
        ( 1-cell-large-lax-transitive-globular-map q)
        ( 1-cell-large-lax-transitive-globular-map p))
      ( 1-cell-large-lax-transitive-globular-map
        ( comp-1-cell-Large-Transitive-Globular-Type G q p))
  preserves-comp-1-cell-large-lax-transitive-globular-map =
    preserves-comp-1-cell-is-lax-transitive-large-globular-map
      is-lax-transitive-large-lax-transitive-globular-map

  is-lax-transitive-1-cell-globular-map-large-lax-transitive-globular-map :
    {l1 l2 : Level}
    {x : 0-cell-Large-Transitive-Globular-Type G l1}
    {y : 0-cell-Large-Transitive-Globular-Type G l2} →
    is-lax-transitive-globular-map
      ( 1-cell-transitive-globular-type-Large-Transitive-Globular-Type G x y)
      ( 1-cell-transitive-globular-type-Large-Transitive-Globular-Type H
        ( 0-cell-large-lax-transitive-globular-map x)
        ( 0-cell-large-lax-transitive-globular-map y))
      ( 1-cell-globular-map-large-lax-transitive-globular-map)
  is-lax-transitive-1-cell-globular-map-large-lax-transitive-globular-map =
    is-lax-transitive-1-cell-globular-map-is-lax-transitive-large-globular-map
      is-lax-transitive-large-lax-transitive-globular-map

  1-cell-large-lax-transitive-large-globular-map-large-lax-transitive-globular-map :
    {l1 l2 : Level}
    {x : 0-cell-Large-Transitive-Globular-Type G l1}
    {y : 0-cell-Large-Transitive-Globular-Type G l2} →
    lax-transitive-globular-map
      ( 1-cell-transitive-globular-type-Large-Transitive-Globular-Type G x y)
      ( 1-cell-transitive-globular-type-Large-Transitive-Globular-Type H
        ( 0-cell-large-lax-transitive-globular-map x)
        ( 0-cell-large-lax-transitive-globular-map y))
  globular-map-lax-transitive-globular-map
    1-cell-large-lax-transitive-large-globular-map-large-lax-transitive-globular-map =
    1-cell-globular-map-large-lax-transitive-globular-map
  is-lax-transitive-lax-transitive-globular-map
    1-cell-large-lax-transitive-large-globular-map-large-lax-transitive-globular-map =
    is-lax-transitive-1-cell-globular-map-large-lax-transitive-globular-map

open large-lax-transitive-globular-map public
```

### Composition of lax transitive maps

```agda
map-comp-large-lax-transitive-globular-map :
  {α1 α2 α3 γ1 γ2 : Level → Level} {β1 β2 β3 : Level → Level → Level}
  (G : Large-Transitive-Globular-Type α1 β1)
  (H : Large-Transitive-Globular-Type α2 β2)
  (K : Large-Transitive-Globular-Type α3 β3)
  (g : large-lax-transitive-globular-map γ2 H K)
  (f : large-lax-transitive-globular-map γ1 G H) →
  large-globular-map-Large-Transitive-Globular-Type (γ2 ∘ γ1) G K
map-comp-large-lax-transitive-globular-map G H K g f =
  comp-large-globular-map
    ( large-globular-map-large-lax-transitive-globular-map g)
    ( large-globular-map-large-lax-transitive-globular-map f)

is-lax-transitive-comp-large-lax-transitive-globular-map :
  {α1 α2 α3 γ1 γ2 : Level → Level} {β1 β2 β3 : Level → Level → Level}
  (G : Large-Transitive-Globular-Type α1 β1)
  (H : Large-Transitive-Globular-Type α2 β2)
  (K : Large-Transitive-Globular-Type α3 β3)
  (g : large-lax-transitive-globular-map γ2 H K)
  (f : large-lax-transitive-globular-map γ1 G H) →
  is-lax-transitive-large-globular-map G K
    ( map-comp-large-lax-transitive-globular-map G H K g f)
preserves-comp-1-cell-is-lax-transitive-large-globular-map
  ( is-lax-transitive-comp-large-lax-transitive-globular-map G H K g f) q p =
  comp-2-cell-Large-Transitive-Globular-Type K
    ( 2-cell-large-lax-transitive-globular-map g
      ( preserves-comp-1-cell-large-lax-transitive-globular-map f q p))
    ( preserves-comp-1-cell-large-lax-transitive-globular-map g _ _)
is-lax-transitive-1-cell-globular-map-is-lax-transitive-large-globular-map
  ( is-lax-transitive-comp-large-lax-transitive-globular-map G H K g f) =
  is-lax-transitive-comp-lax-transitive-globular-map
    ( 1-cell-transitive-globular-type-Large-Transitive-Globular-Type G _ _)
    ( 1-cell-transitive-globular-type-Large-Transitive-Globular-Type H _ _)
    ( 1-cell-transitive-globular-type-Large-Transitive-Globular-Type K _ _)
    ( 1-cell-large-lax-transitive-large-globular-map-large-lax-transitive-globular-map
      g)
    ( 1-cell-large-lax-transitive-large-globular-map-large-lax-transitive-globular-map
      f)
```
