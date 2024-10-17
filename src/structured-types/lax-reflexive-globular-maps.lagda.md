# Lax reflexive globular maps

```agda
{-# OPTIONS --guardedness #-}

module structured-types.lax-reflexive-globular-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import structured-types.globular-maps
open import structured-types.reflexive-globular-types
```

</details>

## Idea

A {{#concept "lax reflexive globular map" Agda=reflexive-globular-map}} between two
[reflexive globular types](structured-types.reflexive-globular-types.md) `G` and
`H` is a [globular map](structured-types.globular-maps.md) `f : G → H` equipped
with a family of 2-cells

```text
  (x : G₀) → H₂ (f₁ (Gᵣ x)) (Hᵣ (f₀ x))
```

from the image of the reflexivity cell at `x` in `G` to the reflexivity cell at `f₀ x`, such that the globular map `f' : G' x y → H' (f₀ x) (f₀ y)` is again lax reflexive.

Note: When reflexive globular types are viewed as type-valued presheaves over the reflexive globe category, the resulting notion of morphism is that of [reflexive globular maps](structured-types.reflexive-globular-maps.md), which is stricter than the notion of lax reflexive globular maps.

## Definitions

### The predicate of lax preserving reflexivity

```agda
record
  lax-preserves-refl-globular-map
    {l1 l2 l3 l4 : Level}
    (G : Reflexive-Globular-Type l1 l2) (H : Reflexive-Globular-Type l3 l4)
    (f : globular-map-Reflexive-Globular-Type G H) :
    UU (l1 ⊔ l2 ⊔ l4)
  where
  coinductive

  field
    lax-preserves-refl-0-cell-lax-preserves-refl-globular-map :
      (x : 0-cell-Reflexive-Globular-Type G) →
      2-cell-Reflexive-Globular-Type H
        ( 1-cell-globular-map f (refl-0-cell-Reflexive-Globular-Type G {x}))
        ( refl-0-cell-Reflexive-Globular-Type H)

  field
    lax-preserves-refl-1-cell-globular-map-globular-map :
      {x y : 0-cell-Reflexive-Globular-Type G} →
      lax-preserves-refl-globular-map
        ( 1-cell-reflexive-globular-type-Reflexive-Globular-Type G x y)
        ( 1-cell-reflexive-globular-type-Reflexive-Globular-Type H _ _)
        ( 1-cell-globular-map-globular-map-Reflexive-Globular-Type G H f)

open lax-preserves-refl-globular-map
```

### Lax reflexive globular maps

```agda
record
  lax-reflexive-globular-map
    {l1 l2 l3 l4 : Level}
    (G : Reflexive-Globular-Type l1 l2)
    (H : Reflexive-Globular-Type l3 l4) :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  where

  field
    globular-map-lax-reflexive-globular-map :
      globular-map-Reflexive-Globular-Type G H

  0-cell-lax-reflexive-globular-map :
    0-cell-Reflexive-Globular-Type G → 0-cell-Reflexive-Globular-Type H
  0-cell-lax-reflexive-globular-map =
    0-cell-globular-map globular-map-lax-reflexive-globular-map

  1-cell-lax-reflexive-globular-map :
    {x y : 0-cell-Reflexive-Globular-Type G} →
    1-cell-Reflexive-Globular-Type G x y →
    1-cell-Reflexive-Globular-Type H
      ( 0-cell-lax-reflexive-globular-map x)
      ( 0-cell-lax-reflexive-globular-map y)
  1-cell-lax-reflexive-globular-map =
    1-cell-globular-map globular-map-lax-reflexive-globular-map

  1-cell-globular-map-lax-reflexive-globular-map :
    {x y : 0-cell-Reflexive-Globular-Type G} →
    globular-map-Reflexive-Globular-Type
      ( 1-cell-reflexive-globular-type-Reflexive-Globular-Type G x y)
      ( 1-cell-reflexive-globular-type-Reflexive-Globular-Type H
        ( 0-cell-lax-reflexive-globular-map x)
        ( 0-cell-lax-reflexive-globular-map y))
  1-cell-globular-map-lax-reflexive-globular-map =
    1-cell-globular-map-globular-map globular-map-lax-reflexive-globular-map

  field
    lax-preserves-refl-lax-reflexive-globular-map :
      lax-preserves-refl-globular-map G H
        globular-map-lax-reflexive-globular-map

  lax-preserves-refl-0-cell-lax-reflexive-globular-map :
    ( x : 0-cell-Reflexive-Globular-Type G) →
    2-cell-Reflexive-Globular-Type H
      ( 1-cell-lax-reflexive-globular-map
        ( refl-0-cell-Reflexive-Globular-Type G {x}))
      ( refl-0-cell-Reflexive-Globular-Type H)
  lax-preserves-refl-0-cell-lax-reflexive-globular-map =
    lax-preserves-refl-0-cell-lax-preserves-refl-globular-map
      lax-preserves-refl-lax-reflexive-globular-map

  lax-preserves-refl-1-cell-globular-map-lax-reflexive-globular-map :
    { x y : 0-cell-Reflexive-Globular-Type G} →
    lax-preserves-refl-globular-map
      ( 1-cell-reflexive-globular-type-Reflexive-Globular-Type G x y)
      ( 1-cell-reflexive-globular-type-Reflexive-Globular-Type H
        ( 0-cell-lax-reflexive-globular-map x)
        ( 0-cell-lax-reflexive-globular-map y))
      ( 1-cell-globular-map-lax-reflexive-globular-map)
  lax-preserves-refl-1-cell-globular-map-lax-reflexive-globular-map =
    lax-preserves-refl-1-cell-globular-map-globular-map
      lax-preserves-refl-lax-reflexive-globular-map

  1-cell-lax-reflexive-globular-map-lax-reflexive-globular-map :
    {x y : 0-cell-Reflexive-Globular-Type G} →
    lax-reflexive-globular-map
      ( 1-cell-reflexive-globular-type-Reflexive-Globular-Type G x y)
      ( 1-cell-reflexive-globular-type-Reflexive-Globular-Type H
        ( 0-cell-lax-reflexive-globular-map x)
        ( 0-cell-lax-reflexive-globular-map y))
  globular-map-lax-reflexive-globular-map
    1-cell-lax-reflexive-globular-map-lax-reflexive-globular-map =
    1-cell-globular-map-lax-reflexive-globular-map
  lax-preserves-refl-lax-reflexive-globular-map
    1-cell-lax-reflexive-globular-map-lax-reflexive-globular-map =
    lax-preserves-refl-1-cell-globular-map-lax-reflexive-globular-map
```
