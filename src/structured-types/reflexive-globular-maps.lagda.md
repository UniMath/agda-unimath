# Reflexive globular maps

```agda
{-# OPTIONS --guardedness #-}

module structured-types.reflexive-globular-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import structured-types.globular-maps
open import structured-types.reflexive-globular-types
```

</details>

## Idea

A {{#concept "reflexive globular map" Agda=reflexive-globular-map}} between two
[reflexive globular types](structured-types.reflexive-globular-types.md) `G` and
`H` is a [globular map](structured-types.globular-maps.md) `f : G → H` equipped
with

## Definitions

### Globular maps between reflexive globular types

```agda
module _
  {l1 l2 l3 l4 : Level}
  (G : Reflexive-Globular-Type l1 l2) (H : Reflexive-Globular-Type l3 l4)
  where

  globular-map-Reflexive-Globular-Type : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  globular-map-Reflexive-Globular-Type =
    globular-map
      ( globular-type-Reflexive-Globular-Type G)
      ( globular-type-Reflexive-Globular-Type H)

module _
  {l1 l2 l3 l4 : Level}
  (G : Reflexive-Globular-Type l1 l2) (H : Reflexive-Globular-Type l3 l4)
  (f : globular-map-Reflexive-Globular-Type G H)
  where

  0-cell-globular-map-Reflexive-Globular-Type :
    0-cell-Reflexive-Globular-Type G → 0-cell-Reflexive-Globular-Type H
  0-cell-globular-map-Reflexive-Globular-Type =
    0-cell-globular-map f

  1-cell-globular-map-globular-map-Reflexive-Globular-Type :
    {x y : 0-cell-Reflexive-Globular-Type G} →
    globular-map-Reflexive-Globular-Type
      ( 1-cell-reflexive-globular-type-Reflexive-Globular-Type G x y)
      ( 1-cell-reflexive-globular-type-Reflexive-Globular-Type H _ _)
  1-cell-globular-map-globular-map-Reflexive-Globular-Type =
    1-cell-globular-map-globular-map f
```

### The predicate of preserving reflexivity

```agda
record
  preserves-refl-globular-map
    {l1 l2 l3 l4 : Level}
    (G : Reflexive-Globular-Type l1 l2) (H : Reflexive-Globular-Type l3 l4)
    (f : globular-map-Reflexive-Globular-Type G H) :
    UU (l1 ⊔ l2 ⊔ l4)
  where
  coinductive

  field
    preserves-refl-0-cell-preserves-refl-globular-map :
      (x : 0-cell-Reflexive-Globular-Type G) →
      2-cell-Reflexive-Globular-Type H
        ( 1-cell-globular-map f (refl-0-cell-Reflexive-Globular-Type G {x}))
        ( refl-0-cell-Reflexive-Globular-Type H)

  field
    preserves-refl-1-cell-globular-map-globular-map :
      {x y : 0-cell-Reflexive-Globular-Type G} →
      preserves-refl-globular-map
        ( 1-cell-reflexive-globular-type-Reflexive-Globular-Type G x y)
        ( 1-cell-reflexive-globular-type-Reflexive-Globular-Type H _ _)
        ( 1-cell-globular-map-globular-map-Reflexive-Globular-Type G H f)

open preserves-refl-globular-map
```

### Reflexive globular maps

```agda
record
  reflexive-globular-map
    {l1 l2 l3 l4 : Level}
    (G : Reflexive-Globular-Type l1 l2)
    (H : Reflexive-Globular-Type l3 l4) :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  where

  field
    globular-map-reflexive-globular-map :
      globular-map-Reflexive-Globular-Type G H

  0-cell-reflexive-globular-map :
    0-cell-Reflexive-Globular-Type G → 0-cell-Reflexive-Globular-Type H
  0-cell-reflexive-globular-map =
    0-cell-globular-map globular-map-reflexive-globular-map

  1-cell-reflexive-globular-map :
    {x y : 0-cell-Reflexive-Globular-Type G} →
    1-cell-Reflexive-Globular-Type G x y →
    1-cell-Reflexive-Globular-Type H
      ( 0-cell-reflexive-globular-map x)
      ( 0-cell-reflexive-globular-map y)
  1-cell-reflexive-globular-map =
    1-cell-globular-map globular-map-reflexive-globular-map

  1-cell-globular-map-reflexive-globular-map :
    {x y : 0-cell-Reflexive-Globular-Type G} →
    globular-map-Reflexive-Globular-Type
      ( 1-cell-reflexive-globular-type-Reflexive-Globular-Type G x y)
      ( 1-cell-reflexive-globular-type-Reflexive-Globular-Type H
        ( 0-cell-reflexive-globular-map x)
        ( 0-cell-reflexive-globular-map y))
  1-cell-globular-map-reflexive-globular-map =
    1-cell-globular-map-globular-map globular-map-reflexive-globular-map

  field
    preserves-refl-reflexive-globular-map :
      preserves-refl-globular-map G H
        globular-map-reflexive-globular-map

  preserves-refl-0-cell-reflexive-globular-map :
    ( x : 0-cell-Reflexive-Globular-Type G) →
    2-cell-Reflexive-Globular-Type H
      ( 1-cell-reflexive-globular-map
        ( refl-0-cell-Reflexive-Globular-Type G {x}))
      ( refl-0-cell-Reflexive-Globular-Type H)
  preserves-refl-0-cell-reflexive-globular-map =
    preserves-refl-0-cell-preserves-refl-globular-map
      preserves-refl-reflexive-globular-map

  preserves-refl-1-cell-globular-map-reflexive-globular-map :
    { x y : 0-cell-Reflexive-Globular-Type G} →
    preserves-refl-globular-map
      ( 1-cell-reflexive-globular-type-Reflexive-Globular-Type G x y)
      ( 1-cell-reflexive-globular-type-Reflexive-Globular-Type H
        ( 0-cell-reflexive-globular-map x)
        ( 0-cell-reflexive-globular-map y))
      ( 1-cell-globular-map-reflexive-globular-map)
  preserves-refl-1-cell-globular-map-reflexive-globular-map =
    preserves-refl-1-cell-globular-map-globular-map
      preserves-refl-reflexive-globular-map

  1-cell-reflexive-globular-map-reflexive-globular-map :
    {x y : 0-cell-Reflexive-Globular-Type G} →
    reflexive-globular-map
      ( 1-cell-reflexive-globular-type-Reflexive-Globular-Type G x y)
      ( 1-cell-reflexive-globular-type-Reflexive-Globular-Type H
        ( 0-cell-reflexive-globular-map x)
        ( 0-cell-reflexive-globular-map y))
  globular-map-reflexive-globular-map
    1-cell-reflexive-globular-map-reflexive-globular-map =
    1-cell-globular-map-reflexive-globular-map
  preserves-refl-reflexive-globular-map
    1-cell-reflexive-globular-map-reflexive-globular-map =
    preserves-refl-1-cell-globular-map-reflexive-globular-map
```
