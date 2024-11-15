# Reflexive globular maps

```agda
{-# OPTIONS --guardedness #-}

module structured-types.reflexive-globular-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-types
open import foundation.universe-levels

open import structured-types.globular-maps
open import structured-types.reflexive-globular-types
```

</details>

## Idea

A {{#concept "reflexive globular map" Agda=reflexive-globular-map}} between two
[reflexive globular types](structured-types.reflexive-globular-types.md) `G` and
`H` is a [globular map](structured-types.globular-maps.md) `f : G → H` equipped
with a family of [identifications](foundation-core.identity-types.md)

```text
  (x : G₀) → f₁ (refl G x) ＝ refl H (f₀ x)
```

from the image of the reflexivity cell at `x` in `G` to the reflexivity cell at
`f₀ x`, such that the globular map `f' : G' x y → H' (f₀ x) (f₀ y)` is again
reflexive.

Note: In some settings it may be preferred to work with globular maps preserving
reflexivity cells up to a higher cell. The two notions of maps between reflexive
globular types preserving the reflexivity structure up to a higher cell are,
depending of the direction of the coherence cells, the notions of
[colax reflexive globular maps](structured-types.colax-reflexive-globular-maps.md)
and
[lax reflexive globular maps](structured-types.lax-reflexive-globular-maps.md).

## Definitions

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
    preserves-refl-1-cell-preserves-refl-globular-map :
      (x : 0-cell-Reflexive-Globular-Type G) →
      1-cell-globular-map f (refl-1-cell-Reflexive-Globular-Type G {x}) ＝
      refl-1-cell-Reflexive-Globular-Type H

  field
    preserves-refl-1-cell-globular-map-preserves-refl-globular-map :
      {x y : 0-cell-Reflexive-Globular-Type G} →
      preserves-refl-globular-map
        ( 1-cell-reflexive-globular-type-Reflexive-Globular-Type G x y)
        ( 1-cell-reflexive-globular-type-Reflexive-Globular-Type H _ _)
        ( 1-cell-globular-map-globular-map-Reflexive-Globular-Type G H f)

open preserves-refl-globular-map public
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

  preserves-refl-1-cell-reflexive-globular-map :
    ( x : 0-cell-Reflexive-Globular-Type G) →
    1-cell-reflexive-globular-map (refl-1-cell-Reflexive-Globular-Type G {x}) ＝
    refl-1-cell-Reflexive-Globular-Type H
  preserves-refl-1-cell-reflexive-globular-map =
    preserves-refl-1-cell-preserves-refl-globular-map
      preserves-refl-reflexive-globular-map

  preserves-refl-2-cell-globular-map-reflexive-globular-map :
    { x y : 0-cell-Reflexive-Globular-Type G} →
    preserves-refl-globular-map
      ( 1-cell-reflexive-globular-type-Reflexive-Globular-Type G x y)
      ( 1-cell-reflexive-globular-type-Reflexive-Globular-Type H
        ( 0-cell-reflexive-globular-map x)
        ( 0-cell-reflexive-globular-map y))
      ( 1-cell-globular-map-reflexive-globular-map)
  preserves-refl-2-cell-globular-map-reflexive-globular-map =
    preserves-refl-1-cell-globular-map-preserves-refl-globular-map
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
    preserves-refl-2-cell-globular-map-reflexive-globular-map

open reflexive-globular-map public
```
