# Transitive globular maps

```agda
{-# OPTIONS --guardedness #-}

module globular-types.transitive-globular-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.identity-types
open import foundation.universe-levels

open import globular-types.globular-maps
open import globular-types.transitive-globular-types
```

</details>

## Idea

A {{#concept "transitive globular map" Agda=transitive-globular-map}} between
two [transitive globular types](globular-types.transitive-globular-types.md) `G`
and `H` is a [globular map](globular-types.globular-maps.md) `f : G → H`
equipped with a family of [identifications](foundation-core.identity-types.md)

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
  is-transitive-globular-map
    {l1 l2 l3 l4 : Level}
    (G : Transitive-Globular-Type l1 l2) (H : Transitive-Globular-Type l3 l4)
    (f : globular-map-Transitive-Globular-Type G H) :
    UU (l1 ⊔ l2 ⊔ l4)
  where
  coinductive

  field
    preserves-comp-1-cell-is-transitive-globular-map :
      {x y z : 0-cell-Transitive-Globular-Type G} →
      (q : 1-cell-Transitive-Globular-Type G y z)
      (p : 1-cell-Transitive-Globular-Type G x y) →
      1-cell-globular-map f (comp-1-cell-Transitive-Globular-Type G q p) ＝
      comp-1-cell-Transitive-Globular-Type H
        ( 1-cell-globular-map f q)
        ( 1-cell-globular-map f p)

  field
    is-transitive-1-cell-globular-map-is-transitive-globular-map :
      {x y : 0-cell-Transitive-Globular-Type G} →
      is-transitive-globular-map
        ( 1-cell-transitive-globular-type-Transitive-Globular-Type G x y)
        ( 1-cell-transitive-globular-type-Transitive-Globular-Type H _ _)
        ( 1-cell-globular-map-globular-map f)

open is-transitive-globular-map public
```

### transitive globular maps

```agda
record
  transitive-globular-map
    {l1 l2 l3 l4 : Level}
    (G : Transitive-Globular-Type l1 l2)
    (H : Transitive-Globular-Type l3 l4) :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  where

  field
    globular-map-transitive-globular-map :
      globular-map-Transitive-Globular-Type G H

  0-cell-transitive-globular-map :
    0-cell-Transitive-Globular-Type G → 0-cell-Transitive-Globular-Type H
  0-cell-transitive-globular-map =
    0-cell-globular-map globular-map-transitive-globular-map

  1-cell-transitive-globular-map :
    {x y : 0-cell-Transitive-Globular-Type G} →
    1-cell-Transitive-Globular-Type G x y →
    1-cell-Transitive-Globular-Type H
      ( 0-cell-transitive-globular-map x)
      ( 0-cell-transitive-globular-map y)
  1-cell-transitive-globular-map =
    1-cell-globular-map globular-map-transitive-globular-map

  1-cell-globular-map-transitive-globular-map :
    {x y : 0-cell-Transitive-Globular-Type G} →
    globular-map-Transitive-Globular-Type
      ( 1-cell-transitive-globular-type-Transitive-Globular-Type G x y)
      ( 1-cell-transitive-globular-type-Transitive-Globular-Type H
        ( 0-cell-transitive-globular-map x)
        ( 0-cell-transitive-globular-map y))
  1-cell-globular-map-transitive-globular-map =
    1-cell-globular-map-globular-map globular-map-transitive-globular-map

  2-cell-transitive-globular-map :
    {x y : 0-cell-Transitive-Globular-Type G}
    {f g : 1-cell-Transitive-Globular-Type G x y} →
    2-cell-Transitive-Globular-Type G f g →
    2-cell-Transitive-Globular-Type H
      ( 1-cell-transitive-globular-map f)
      ( 1-cell-transitive-globular-map g)
  2-cell-transitive-globular-map =
    2-cell-globular-map globular-map-transitive-globular-map

  2-cell-globular-map-transitive-globular-map :
    {x y : 0-cell-Transitive-Globular-Type G}
    {f g : 1-cell-Transitive-Globular-Type G x y} →
    globular-map-Transitive-Globular-Type
      ( 2-cell-transitive-globular-type-Transitive-Globular-Type G f g)
      ( 2-cell-transitive-globular-type-Transitive-Globular-Type H
        ( 1-cell-transitive-globular-map f)
        ( 1-cell-transitive-globular-map g))
  2-cell-globular-map-transitive-globular-map =
    2-cell-globular-map-globular-map
      ( globular-map-transitive-globular-map)
      ( _)
      ( _)

  field
    is-transitive-transitive-globular-map :
      is-transitive-globular-map G H
        globular-map-transitive-globular-map

  preserves-comp-1-cell-transitive-globular-map :
    {x y z : 0-cell-Transitive-Globular-Type G}
    (q : 1-cell-Transitive-Globular-Type G y z)
    (p : 1-cell-Transitive-Globular-Type G x y) →
    1-cell-transitive-globular-map
      ( comp-1-cell-Transitive-Globular-Type G q p) ＝
    comp-1-cell-Transitive-Globular-Type H
      ( 1-cell-transitive-globular-map q)
      ( 1-cell-transitive-globular-map p)
  preserves-comp-1-cell-transitive-globular-map =
    preserves-comp-1-cell-is-transitive-globular-map
      is-transitive-transitive-globular-map

  is-transitive-1-cell-globular-map-transitive-globular-map :
    { x y : 0-cell-Transitive-Globular-Type G} →
    is-transitive-globular-map
      ( 1-cell-transitive-globular-type-Transitive-Globular-Type G x y)
      ( 1-cell-transitive-globular-type-Transitive-Globular-Type H
        ( 0-cell-transitive-globular-map x)
        ( 0-cell-transitive-globular-map y))
      ( 1-cell-globular-map-transitive-globular-map)
  is-transitive-1-cell-globular-map-transitive-globular-map =
    is-transitive-1-cell-globular-map-is-transitive-globular-map
      is-transitive-transitive-globular-map

  1-cell-transitive-globular-map-transitive-globular-map :
    {x y : 0-cell-Transitive-Globular-Type G} →
    transitive-globular-map
      ( 1-cell-transitive-globular-type-Transitive-Globular-Type G x y)
      ( 1-cell-transitive-globular-type-Transitive-Globular-Type H
        ( 0-cell-transitive-globular-map x)
        ( 0-cell-transitive-globular-map y))
  globular-map-transitive-globular-map
    1-cell-transitive-globular-map-transitive-globular-map =
    1-cell-globular-map-transitive-globular-map
  is-transitive-transitive-globular-map
    1-cell-transitive-globular-map-transitive-globular-map =
    is-transitive-1-cell-globular-map-transitive-globular-map

open transitive-globular-map public
```

### Composition of transitive maps

```agda
map-comp-transitive-globular-map :
  {l1 l2 l3 l4 l5 l6 : Level}
  (G : Transitive-Globular-Type l1 l2)
  (H : Transitive-Globular-Type l3 l4)
  (K : Transitive-Globular-Type l5 l6) →
  transitive-globular-map H K → transitive-globular-map G H →
  globular-map-Transitive-Globular-Type G K
map-comp-transitive-globular-map G H K g f =
  comp-globular-map
    ( globular-map-transitive-globular-map g)
    ( globular-map-transitive-globular-map f)

is-transitive-comp-transitive-globular-map :
  {l1 l2 l3 l4 l5 l6 : Level}
  (G : Transitive-Globular-Type l1 l2)
  (H : Transitive-Globular-Type l3 l4)
  (K : Transitive-Globular-Type l5 l6) →
  (g : transitive-globular-map H K)
  (f : transitive-globular-map G H) →
  is-transitive-globular-map G K
    ( map-comp-transitive-globular-map G H K g f)
preserves-comp-1-cell-is-transitive-globular-map
  ( is-transitive-comp-transitive-globular-map G H K g f) q p =
  ( ap
    ( 1-cell-transitive-globular-map g)
    ( preserves-comp-1-cell-transitive-globular-map f q p)) ∙
  ( preserves-comp-1-cell-transitive-globular-map g _ _)
is-transitive-1-cell-globular-map-is-transitive-globular-map
  ( is-transitive-comp-transitive-globular-map G H K g f) =
  is-transitive-comp-transitive-globular-map
    ( 1-cell-transitive-globular-type-Transitive-Globular-Type G _ _)
    ( 1-cell-transitive-globular-type-Transitive-Globular-Type H _ _)
    ( 1-cell-transitive-globular-type-Transitive-Globular-Type K _ _)
    ( 1-cell-transitive-globular-map-transitive-globular-map g)
    ( 1-cell-transitive-globular-map-transitive-globular-map f)
```
