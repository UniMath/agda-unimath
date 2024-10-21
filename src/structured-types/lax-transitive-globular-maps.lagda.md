# Lax transitive globular maps

```agda
{-# OPTIONS --guardedness #-}

module structured-types.lax-transitive-globular-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import structured-types.globular-maps
open import structured-types.transitive-globular-types
```

</details>

## Idea

A {{#concept "lax transitive globular map" Agda=lax-transitive-globular-map}}
between two
[transitive globular types](structured-types.transitive-globular-types.md) `G`
and `H` is a [globular map](structured-types.globular-maps.md) `f : G → H`
equipped with a family of 2-cells

```text
  H₂ (f₁ (q ∘G p)) (f₁ q ∘H f₁ p)
```

from the image of the composite of two 1-cells `q` and `p` in `G` to the
composite of `f₁ q` and `f₁ p` in `H`, such that the globular map
`f' : G' x y → H' (f₀ x) (f₀ y)` is again lax transitive.

### Lack of identity lax transitive globular maps

Note that the lax transitive globular maps lack an identity morphism. For an
identity morphism to exist on a transitive globular type `G`, there should be a
`2`-cell from `q ∘G p` to `q ∘G p` for every composable pair of `1`-cells `q`
and `p`. However, since the transitive globular type `G` is not assumed to be
[reflexive](structured-types.reflexive-globular-types.md), it might lack such
instances of the reflexivity cells.

## Definitions

### The predicate of lax preserving transitivity

```agda
record
  is-lax-transitive-globular-map
    {l1 l2 l3 l4 : Level}
    (G : Transitive-Globular-Type l1 l2) (H : Transitive-Globular-Type l3 l4)
    (f : globular-map-Transitive-Globular-Type G H) :
    UU (l1 ⊔ l2 ⊔ l4)
  where
  coinductive

  field
    preserves-comp-1-cell-is-lax-transitive-globular-map :
      {x y z : 0-cell-Transitive-Globular-Type G} →
      (q : 1-cell-Transitive-Globular-Type G y z)
      (p : 1-cell-Transitive-Globular-Type G x y) →
      2-cell-Transitive-Globular-Type H
        ( comp-1-cell-Transitive-Globular-Type H
          ( 1-cell-globular-map f q)
          ( 1-cell-globular-map f p))
        ( 1-cell-globular-map f
          ( comp-1-cell-Transitive-Globular-Type G q p))

  field
    is-lax-transitive-1-cell-globular-map-is-lax-transitive-globular-map :
      {x y : 0-cell-Transitive-Globular-Type G} →
      is-lax-transitive-globular-map
        ( 1-cell-transitive-globular-type-Transitive-Globular-Type G x y)
        ( 1-cell-transitive-globular-type-Transitive-Globular-Type H _ _)
        ( 1-cell-globular-map-globular-map f)

open is-lax-transitive-globular-map public
```

### Lax transitive globular maps

```agda
record
  lax-transitive-globular-map
    {l1 l2 l3 l4 : Level}
    (G : Transitive-Globular-Type l1 l2)
    (H : Transitive-Globular-Type l3 l4) :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  where

  field
    globular-map-lax-transitive-globular-map :
      globular-map-Transitive-Globular-Type G H

  0-cell-lax-transitive-globular-map :
    0-cell-Transitive-Globular-Type G → 0-cell-Transitive-Globular-Type H
  0-cell-lax-transitive-globular-map =
    0-cell-globular-map globular-map-lax-transitive-globular-map

  1-cell-lax-transitive-globular-map :
    {x y : 0-cell-Transitive-Globular-Type G} →
    1-cell-Transitive-Globular-Type G x y →
    1-cell-Transitive-Globular-Type H
      ( 0-cell-lax-transitive-globular-map x)
      ( 0-cell-lax-transitive-globular-map y)
  1-cell-lax-transitive-globular-map =
    1-cell-globular-map globular-map-lax-transitive-globular-map

  1-cell-globular-map-lax-transitive-globular-map :
    {x y : 0-cell-Transitive-Globular-Type G} →
    globular-map-Transitive-Globular-Type
      ( 1-cell-transitive-globular-type-Transitive-Globular-Type G x y)
      ( 1-cell-transitive-globular-type-Transitive-Globular-Type H
        ( 0-cell-lax-transitive-globular-map x)
        ( 0-cell-lax-transitive-globular-map y))
  1-cell-globular-map-lax-transitive-globular-map =
    1-cell-globular-map-globular-map globular-map-lax-transitive-globular-map

  2-cell-lax-transitive-globular-map :
    {x y : 0-cell-Transitive-Globular-Type G}
    {f g : 1-cell-Transitive-Globular-Type G x y} →
    2-cell-Transitive-Globular-Type G f g →
    2-cell-Transitive-Globular-Type H
      ( 1-cell-lax-transitive-globular-map f)
      ( 1-cell-lax-transitive-globular-map g)
  2-cell-lax-transitive-globular-map =
    2-cell-globular-map globular-map-lax-transitive-globular-map

  2-cell-globular-map-lax-transitive-globular-map :
    {x y : 0-cell-Transitive-Globular-Type G}
    {f g : 1-cell-Transitive-Globular-Type G x y} →
    globular-map-Transitive-Globular-Type
      ( 2-cell-transitive-globular-type-Transitive-Globular-Type G f g)
      ( 2-cell-transitive-globular-type-Transitive-Globular-Type H
        ( 1-cell-lax-transitive-globular-map f)
        ( 1-cell-lax-transitive-globular-map g))
  2-cell-globular-map-lax-transitive-globular-map =
    2-cell-globular-map-globular-map
      ( globular-map-lax-transitive-globular-map)
      ( _)
      ( _)

  field
    is-lax-transitive-lax-transitive-globular-map :
      is-lax-transitive-globular-map G H
        globular-map-lax-transitive-globular-map

  preserves-comp-1-cell-lax-transitive-globular-map :
    {x y z : 0-cell-Transitive-Globular-Type G}
    (q : 1-cell-Transitive-Globular-Type G y z)
    (p : 1-cell-Transitive-Globular-Type G x y) →
    2-cell-Transitive-Globular-Type H
      ( comp-1-cell-Transitive-Globular-Type H
        ( 1-cell-lax-transitive-globular-map q)
        ( 1-cell-lax-transitive-globular-map p))
      ( 1-cell-lax-transitive-globular-map
        ( comp-1-cell-Transitive-Globular-Type G q p))
  preserves-comp-1-cell-lax-transitive-globular-map =
    preserves-comp-1-cell-is-lax-transitive-globular-map
      is-lax-transitive-lax-transitive-globular-map

  is-lax-transitive-1-cell-globular-map-lax-transitive-globular-map :
    { x y : 0-cell-Transitive-Globular-Type G} →
    is-lax-transitive-globular-map
      ( 1-cell-transitive-globular-type-Transitive-Globular-Type G x y)
      ( 1-cell-transitive-globular-type-Transitive-Globular-Type H
        ( 0-cell-lax-transitive-globular-map x)
        ( 0-cell-lax-transitive-globular-map y))
      ( 1-cell-globular-map-lax-transitive-globular-map)
  is-lax-transitive-1-cell-globular-map-lax-transitive-globular-map =
    is-lax-transitive-1-cell-globular-map-is-lax-transitive-globular-map
      is-lax-transitive-lax-transitive-globular-map

  1-cell-lax-transitive-globular-map-lax-transitive-globular-map :
    {x y : 0-cell-Transitive-Globular-Type G} →
    lax-transitive-globular-map
      ( 1-cell-transitive-globular-type-Transitive-Globular-Type G x y)
      ( 1-cell-transitive-globular-type-Transitive-Globular-Type H
        ( 0-cell-lax-transitive-globular-map x)
        ( 0-cell-lax-transitive-globular-map y))
  globular-map-lax-transitive-globular-map
    1-cell-lax-transitive-globular-map-lax-transitive-globular-map =
    1-cell-globular-map-lax-transitive-globular-map
  is-lax-transitive-lax-transitive-globular-map
    1-cell-lax-transitive-globular-map-lax-transitive-globular-map =
    is-lax-transitive-1-cell-globular-map-lax-transitive-globular-map

open lax-transitive-globular-map public
```

### Composition of lax transitive maps

```agda
map-comp-lax-transitive-globular-map :
  {l1 l2 l3 l4 l5 l6 : Level}
  (G : Transitive-Globular-Type l1 l2)
  (H : Transitive-Globular-Type l3 l4)
  (K : Transitive-Globular-Type l5 l6) →
  lax-transitive-globular-map H K → lax-transitive-globular-map G H →
  globular-map-Transitive-Globular-Type G K
map-comp-lax-transitive-globular-map G H K g f =
  comp-globular-map
    ( globular-map-lax-transitive-globular-map g)
    ( globular-map-lax-transitive-globular-map f)

is-lax-transitive-comp-lax-transitive-globular-map :
  {l1 l2 l3 l4 l5 l6 : Level}
  (G : Transitive-Globular-Type l1 l2)
  (H : Transitive-Globular-Type l3 l4)
  (K : Transitive-Globular-Type l5 l6) →
  (g : lax-transitive-globular-map H K)
  (f : lax-transitive-globular-map G H) →
  is-lax-transitive-globular-map G K
    ( map-comp-lax-transitive-globular-map G H K g f)
preserves-comp-1-cell-is-lax-transitive-globular-map
  ( is-lax-transitive-comp-lax-transitive-globular-map G H K g f) q p =
  comp-2-cell-Transitive-Globular-Type K
    ( 2-cell-lax-transitive-globular-map g
      ( preserves-comp-1-cell-lax-transitive-globular-map f q p))
    ( preserves-comp-1-cell-lax-transitive-globular-map g _ _)
is-lax-transitive-1-cell-globular-map-is-lax-transitive-globular-map
  ( is-lax-transitive-comp-lax-transitive-globular-map G H K g f) =
  is-lax-transitive-comp-lax-transitive-globular-map
    ( 1-cell-transitive-globular-type-Transitive-Globular-Type G _ _)
    ( 1-cell-transitive-globular-type-Transitive-Globular-Type H _ _)
    ( 1-cell-transitive-globular-type-Transitive-Globular-Type K _ _)
    ( 1-cell-lax-transitive-globular-map-lax-transitive-globular-map g)
    ( 1-cell-lax-transitive-globular-map-lax-transitive-globular-map f)
```
