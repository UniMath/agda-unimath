# Large transitive globular maps

```agda
{-# OPTIONS --guardedness #-}

module structured-types.large-transitive-globular-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.function-types
open import foundation.identity-types
open import foundation.universe-levels

open import structured-types.large-globular-maps
open import structured-types.large-transitive-globular-types
open import structured-types.transitive-globular-maps
open import structured-types.transitive-globular-types
```

</details>

## Idea

A
{{#concept "large transitive globular map" Agda=large-transitive-globular-map}}
between two
[large transitive globular types](structured-types.large-transitive-globular-types.md)
`G` and `H` is a [large globular map](structured-types.large-globular-maps.md)
`f : G → H` equipped with a family of
[identifications](foundation-core.identity-types.md)

```text
  f₁ (q ∘G p) ＝ f₁ q ∘H f₁ p
```

from the image of the composite of two 1-cells `q` and `p` in `G` to the
composite of `f₁ q` and `f₁ p` in `H`, such that the globular map
`f' : G' x y → H' (f₀ x) (f₀ y)` is again transitive.

## Definitions

### The predicate of preserving transitivity

```agda
record
  is-transitive-large-globular-map
    {α1 α2 : Level → Level} {β1 β2 : Level → Level → Level} {γ : Level → Level}
    (G : Large-Transitive-Globular-Type α1 β1)
    (H : Large-Transitive-Globular-Type α2 β2)
    (f : large-globular-map-Large-Transitive-Globular-Type γ G H) : UUω
  where
  coinductive

  field
    preserves-comp-1-cell-is-transitive-large-globular-map :
      {l1 l2 l3 : Level}
      {x : 0-cell-Large-Transitive-Globular-Type G l1}
      {y : 0-cell-Large-Transitive-Globular-Type G l2}
      {z : 0-cell-Large-Transitive-Globular-Type G l3} →
      (q : 1-cell-Large-Transitive-Globular-Type G y z)
      (p : 1-cell-Large-Transitive-Globular-Type G x y) →
      1-cell-large-globular-map f
        ( comp-1-cell-Large-Transitive-Globular-Type G q p) ＝
      comp-1-cell-Large-Transitive-Globular-Type H
        ( 1-cell-large-globular-map f q)
        ( 1-cell-large-globular-map f p)

  field
    is-transitive-1-cell-globular-map-is-transitive-large-globular-map :
      {l1 l2 : Level}
      {x : 0-cell-Large-Transitive-Globular-Type G l1}
      {y : 0-cell-Large-Transitive-Globular-Type G l2} →
      is-transitive-globular-map
        ( 1-cell-transitive-globular-type-Large-Transitive-Globular-Type G x y)
        ( 1-cell-transitive-globular-type-Large-Transitive-Globular-Type H _ _)
        ( 1-cell-globular-map-large-globular-map f)

open is-transitive-large-globular-map public
```

### transitive globular maps

```agda
record
  large-transitive-globular-map
    {α1 α2 : Level → Level} {β1 β2 : Level → Level → Level} (γ : Level → Level)
    (G : Large-Transitive-Globular-Type α1 β1)
    (H : Large-Transitive-Globular-Type α2 β2) : UUω
  where

  field
    large-globular-map-large-transitive-globular-map :
      large-globular-map-Large-Transitive-Globular-Type γ G H

  0-cell-large-transitive-globular-map :
    {l1 : Level} →
    0-cell-Large-Transitive-Globular-Type G l1 →
    0-cell-Large-Transitive-Globular-Type H (γ l1)
  0-cell-large-transitive-globular-map =
    0-cell-large-globular-map large-globular-map-large-transitive-globular-map

  1-cell-large-transitive-globular-map :
    {l1 l2 : Level}
    {x : 0-cell-Large-Transitive-Globular-Type G l1}
    {y : 0-cell-Large-Transitive-Globular-Type G l2} →
    1-cell-Large-Transitive-Globular-Type G x y →
    1-cell-Large-Transitive-Globular-Type H
      ( 0-cell-large-transitive-globular-map x)
      ( 0-cell-large-transitive-globular-map y)
  1-cell-large-transitive-globular-map =
    1-cell-large-globular-map
      large-globular-map-large-transitive-globular-map

  1-cell-globular-map-large-transitive-globular-map :
    {l1 l2 : Level}
    {x : 0-cell-Large-Transitive-Globular-Type G l1}
    {y : 0-cell-Large-Transitive-Globular-Type G l2} →
    globular-map-Transitive-Globular-Type
      ( 1-cell-transitive-globular-type-Large-Transitive-Globular-Type G x y)
      ( 1-cell-transitive-globular-type-Large-Transitive-Globular-Type H
        ( 0-cell-large-transitive-globular-map x)
        ( 0-cell-large-transitive-globular-map y))
  1-cell-globular-map-large-transitive-globular-map =
    1-cell-globular-map-large-globular-map
      large-globular-map-large-transitive-globular-map

  2-cell-large-transitive-globular-map :
    {l1 l2 : Level}
    {x : 0-cell-Large-Transitive-Globular-Type G l1}
    {y : 0-cell-Large-Transitive-Globular-Type G l2} →
    {f g : 1-cell-Large-Transitive-Globular-Type G x y} →
    2-cell-Large-Transitive-Globular-Type G f g →
    2-cell-Large-Transitive-Globular-Type H
      ( 1-cell-large-transitive-globular-map f)
      ( 1-cell-large-transitive-globular-map g)
  2-cell-large-transitive-globular-map =
    2-cell-large-globular-map
      large-globular-map-large-transitive-globular-map

  2-cell-globular-map-large-transitive-globular-map :
    {l1 l2 : Level}
    {x : 0-cell-Large-Transitive-Globular-Type G l1}
    {y : 0-cell-Large-Transitive-Globular-Type G l2} →
    {f g : 1-cell-Large-Transitive-Globular-Type G x y} →
    globular-map-Transitive-Globular-Type
      ( 2-cell-transitive-globular-type-Large-Transitive-Globular-Type G f g)
      ( 2-cell-transitive-globular-type-Large-Transitive-Globular-Type H
        ( 1-cell-large-transitive-globular-map f)
        ( 1-cell-large-transitive-globular-map g))
  2-cell-globular-map-large-transitive-globular-map =
    2-cell-globular-map-large-globular-map
      ( large-globular-map-large-transitive-globular-map)
      ( _)
      ( _)

  field
    is-transitive-large-transitive-globular-map :
      is-transitive-large-globular-map G H
        large-globular-map-large-transitive-globular-map

  preserves-comp-1-cell-large-transitive-globular-map :
    {l1 l2 l3 : Level}
    {x : 0-cell-Large-Transitive-Globular-Type G l1}
    {y : 0-cell-Large-Transitive-Globular-Type G l2}
    {z : 0-cell-Large-Transitive-Globular-Type G l3}
    (q : 1-cell-Large-Transitive-Globular-Type G y z)
    (p : 1-cell-Large-Transitive-Globular-Type G x y) →
    1-cell-large-transitive-globular-map
      ( comp-1-cell-Large-Transitive-Globular-Type G q p) ＝
    comp-1-cell-Large-Transitive-Globular-Type H
      ( 1-cell-large-transitive-globular-map q)
      ( 1-cell-large-transitive-globular-map p)
  preserves-comp-1-cell-large-transitive-globular-map =
    preserves-comp-1-cell-is-transitive-large-globular-map
      is-transitive-large-transitive-globular-map

  is-transitive-1-cell-globular-map-large-transitive-globular-map :
    {l1 l2 : Level}
    {x : 0-cell-Large-Transitive-Globular-Type G l1}
    {y : 0-cell-Large-Transitive-Globular-Type G l2} →
    is-transitive-globular-map
      ( 1-cell-transitive-globular-type-Large-Transitive-Globular-Type G x y)
      ( 1-cell-transitive-globular-type-Large-Transitive-Globular-Type H
        ( 0-cell-large-transitive-globular-map x)
        ( 0-cell-large-transitive-globular-map y))
      ( 1-cell-globular-map-large-transitive-globular-map)
  is-transitive-1-cell-globular-map-large-transitive-globular-map =
    is-transitive-1-cell-globular-map-is-transitive-large-globular-map
      is-transitive-large-transitive-globular-map

  1-cell-large-transitive-large-globular-map-large-transitive-globular-map :
    {l1 l2 : Level}
    {x : 0-cell-Large-Transitive-Globular-Type G l1}
    {y : 0-cell-Large-Transitive-Globular-Type G l2} →
    transitive-globular-map
      ( 1-cell-transitive-globular-type-Large-Transitive-Globular-Type G x y)
      ( 1-cell-transitive-globular-type-Large-Transitive-Globular-Type H
        ( 0-cell-large-transitive-globular-map x)
        ( 0-cell-large-transitive-globular-map y))
  globular-map-transitive-globular-map
    1-cell-large-transitive-large-globular-map-large-transitive-globular-map =
    1-cell-globular-map-large-transitive-globular-map
  is-transitive-transitive-globular-map
    1-cell-large-transitive-large-globular-map-large-transitive-globular-map =
    is-transitive-1-cell-globular-map-large-transitive-globular-map

open large-transitive-globular-map public
```

### Composition of transitive maps

```agda
map-comp-large-transitive-globular-map :
  {α1 α2 α3 γ1 γ2 : Level → Level} {β1 β2 β3 : Level → Level → Level}
  (G : Large-Transitive-Globular-Type α1 β1)
  (H : Large-Transitive-Globular-Type α2 β2)
  (K : Large-Transitive-Globular-Type α3 β3)
  (g : large-transitive-globular-map γ2 H K)
  (f : large-transitive-globular-map γ1 G H) →
  large-globular-map-Large-Transitive-Globular-Type (γ2 ∘ γ1) G K
map-comp-large-transitive-globular-map G H K g f =
  comp-large-globular-map
    ( large-globular-map-large-transitive-globular-map g)
    ( large-globular-map-large-transitive-globular-map f)

is-transitive-comp-large-transitive-globular-map :
  {α1 α2 α3 γ1 γ2 : Level → Level} {β1 β2 β3 : Level → Level → Level}
  (G : Large-Transitive-Globular-Type α1 β1)
  (H : Large-Transitive-Globular-Type α2 β2)
  (K : Large-Transitive-Globular-Type α3 β3)
  (g : large-transitive-globular-map γ2 H K)
  (f : large-transitive-globular-map γ1 G H) →
  is-transitive-large-globular-map G K
    ( map-comp-large-transitive-globular-map G H K g f)
preserves-comp-1-cell-is-transitive-large-globular-map
  ( is-transitive-comp-large-transitive-globular-map G H K g f) q p =
  ( ap (1-cell-large-transitive-globular-map g)
    ( preserves-comp-1-cell-large-transitive-globular-map f q p)) ∙
  ( preserves-comp-1-cell-large-transitive-globular-map g _ _)
is-transitive-1-cell-globular-map-is-transitive-large-globular-map
  ( is-transitive-comp-large-transitive-globular-map G H K g f) =
  is-transitive-comp-transitive-globular-map
    ( 1-cell-transitive-globular-type-Large-Transitive-Globular-Type G _ _)
    ( 1-cell-transitive-globular-type-Large-Transitive-Globular-Type H _ _)
    ( 1-cell-transitive-globular-type-Large-Transitive-Globular-Type K _ _)
    ( 1-cell-large-transitive-large-globular-map-large-transitive-globular-map
      g)
    ( 1-cell-large-transitive-large-globular-map-large-transitive-globular-map
      f)
```
