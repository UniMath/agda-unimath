# Colaxly reflexive globular maps

```agda
{-# OPTIONS --guardedness #-}

module structured-types.colaxly-reflexive-globular-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import structured-types.globular-maps
open import structured-types.reflexive-globular-types
```

</details>

## Idea

A
{{#concept "colaxly reflexive globular map" Agda=colaxly-reflexive-globular-map}}
between two
[reflexive globular types](structured-types.reflexive-globular-types.md) `G` and
`H` is a [globular map](structured-types.globular-maps.md) `f : G → H` equipped
with a family of 2-cells

```text
  (x : G₀) → H₂ (f₁ (Gᵣ x)) (Hᵣ (f₀ x))
```

from the image of the reflexivity cell at `x` in `G` to the reflexivity cell at
`f₀ x`, such that the globular map `f' : G' x y → H' (f₀ x) (f₀ y)` is again
colaxly reflexive.

### Lack of composition for colaxly reflexive globular maps

Note that the colaxly reflexive globular maps lack composition. For the
composition of `g` and `f` to exist, there should be a `2`-cell from
`g (f (refl G x))` to `refl K (g (f x))`, we need to compose the 2-cell that `g`
preserves reflexivity with the action of `g` on the 2-cell that `f` preserves
reflexivity. However, since the reflexive globular type `G` is not assumed to be
[transitive](structured-types.transitive-globular-types.md), it might lack such
instances of the compositions.

### Colaxly reflexive globular maps versus the morphisms of presheaves on the reflexive globe category

When reflexive globular types are viewed as type valued presheaves over the
reflexive globe category, the resulting notion of morphism is that of
[reflexive globular maps](structured-types.reflexive-globular-maps.md), which is
stricter than the notion of colaxly reflexive globular maps.

### Lax versus colax

The notion of
[laxly reflexive globular map](structured-types.laxly-reflexive-globular-maps.md)
is almost the same, except with the direction of the 2-cell reversed. In
general, the direction of lax coherence cells is determined by applying the
morphism componentwise first, and then the operations, while the direction of
colax coherence cells is determined by first applying the operations and then
the morphism.

## Definitions

### The predicate of colaxly preserving reflexivity

```agda
record
  is-colaxly-reflexive-globular-map
    {l1 l2 l3 l4 : Level}
    (G : Reflexive-Globular-Type l1 l2) (H : Reflexive-Globular-Type l3 l4)
    (f : globular-map-Reflexive-Globular-Type G H) :
    UU (l1 ⊔ l2 ⊔ l4)
  where
  coinductive

  field
    preserves-refl-1-cell-is-colaxly-reflexive-globular-map :
      (x : 0-cell-Reflexive-Globular-Type G) →
      2-cell-Reflexive-Globular-Type H
        ( 1-cell-globular-map f (refl-1-cell-Reflexive-Globular-Type G {x}))
        ( refl-1-cell-Reflexive-Globular-Type H)

  field
    is-colaxly-reflexive-1-cell-globular-map-is-colaxly-reflexive-globular-map :
      {x y : 0-cell-Reflexive-Globular-Type G} →
      is-colaxly-reflexive-globular-map
        ( 1-cell-reflexive-globular-type-Reflexive-Globular-Type G x y)
        ( 1-cell-reflexive-globular-type-Reflexive-Globular-Type H _ _)
        ( 1-cell-globular-map-globular-map-Reflexive-Globular-Type G H f)

open is-colaxly-reflexive-globular-map public
```

### Colaxly reflexive globular maps

```agda
record
  colaxly-reflexive-globular-map
    {l1 l2 l3 l4 : Level}
    (G : Reflexive-Globular-Type l1 l2)
    (H : Reflexive-Globular-Type l3 l4) :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  where

  field
    globular-map-colaxly-reflexive-globular-map :
      globular-map-Reflexive-Globular-Type G H

  0-cell-colaxly-reflexive-globular-map :
    0-cell-Reflexive-Globular-Type G → 0-cell-Reflexive-Globular-Type H
  0-cell-colaxly-reflexive-globular-map =
    0-cell-globular-map globular-map-colaxly-reflexive-globular-map

  1-cell-colaxly-reflexive-globular-map :
    {x y : 0-cell-Reflexive-Globular-Type G} →
    1-cell-Reflexive-Globular-Type G x y →
    1-cell-Reflexive-Globular-Type H
      ( 0-cell-colaxly-reflexive-globular-map x)
      ( 0-cell-colaxly-reflexive-globular-map y)
  1-cell-colaxly-reflexive-globular-map =
    1-cell-globular-map globular-map-colaxly-reflexive-globular-map

  1-cell-globular-map-colaxly-reflexive-globular-map :
    {x y : 0-cell-Reflexive-Globular-Type G} →
    globular-map-Reflexive-Globular-Type
      ( 1-cell-reflexive-globular-type-Reflexive-Globular-Type G x y)
      ( 1-cell-reflexive-globular-type-Reflexive-Globular-Type H
        ( 0-cell-colaxly-reflexive-globular-map x)
        ( 0-cell-colaxly-reflexive-globular-map y))
  1-cell-globular-map-colaxly-reflexive-globular-map =
    1-cell-globular-map-globular-map globular-map-colaxly-reflexive-globular-map

  field
    is-colaxly-reflexive-colaxly-reflexive-globular-map :
      is-colaxly-reflexive-globular-map G H
        globular-map-colaxly-reflexive-globular-map

  preserves-refl-1-cell-colaxly-reflexive-globular-map :
    ( x : 0-cell-Reflexive-Globular-Type G) →
    2-cell-Reflexive-Globular-Type H
      ( 1-cell-colaxly-reflexive-globular-map
        ( refl-1-cell-Reflexive-Globular-Type G {x}))
      ( refl-1-cell-Reflexive-Globular-Type H)
  preserves-refl-1-cell-colaxly-reflexive-globular-map =
    preserves-refl-1-cell-is-colaxly-reflexive-globular-map
      is-colaxly-reflexive-colaxly-reflexive-globular-map

  is-colaxly-reflexive-2-cell-globular-map-is-colaxly-reflexive-globular-map :
    { x y : 0-cell-Reflexive-Globular-Type G} →
    is-colaxly-reflexive-globular-map
      ( 1-cell-reflexive-globular-type-Reflexive-Globular-Type G x y)
      ( 1-cell-reflexive-globular-type-Reflexive-Globular-Type H
        ( 0-cell-colaxly-reflexive-globular-map x)
        ( 0-cell-colaxly-reflexive-globular-map y))
      ( 1-cell-globular-map-colaxly-reflexive-globular-map)
  is-colaxly-reflexive-2-cell-globular-map-is-colaxly-reflexive-globular-map =
    is-colaxly-reflexive-1-cell-globular-map-is-colaxly-reflexive-globular-map
      is-colaxly-reflexive-colaxly-reflexive-globular-map

  1-cell-colaxly-reflexive-globular-map-colaxly-reflexive-globular-map :
    {x y : 0-cell-Reflexive-Globular-Type G} →
    colaxly-reflexive-globular-map
      ( 1-cell-reflexive-globular-type-Reflexive-Globular-Type G x y)
      ( 1-cell-reflexive-globular-type-Reflexive-Globular-Type H
        ( 0-cell-colaxly-reflexive-globular-map x)
        ( 0-cell-colaxly-reflexive-globular-map y))
  globular-map-colaxly-reflexive-globular-map
    1-cell-colaxly-reflexive-globular-map-colaxly-reflexive-globular-map =
    1-cell-globular-map-colaxly-reflexive-globular-map
  is-colaxly-reflexive-colaxly-reflexive-globular-map
    1-cell-colaxly-reflexive-globular-map-colaxly-reflexive-globular-map =
    is-colaxly-reflexive-2-cell-globular-map-is-colaxly-reflexive-globular-map

open colaxly-reflexive-globular-map public
```

### The identity colaxly reflexive globular map

```agda
map-id-colaxly-reflexive-globular-map :
  {l1 l2 : Level} (G : Reflexive-Globular-Type l1 l2) →
  globular-map-Reflexive-Globular-Type G G
map-id-colaxly-reflexive-globular-map G = id-globular-map _

is-colaxly-reflexive-id-colaxly-reflexive-globular-map :
  {l1 l2 : Level} (G : Reflexive-Globular-Type l1 l2) →
  is-colaxly-reflexive-globular-map G G
    ( map-id-colaxly-reflexive-globular-map G)
preserves-refl-1-cell-is-colaxly-reflexive-globular-map
  ( is-colaxly-reflexive-id-colaxly-reflexive-globular-map G)
  x =
  refl-2-cell-Reflexive-Globular-Type G
is-colaxly-reflexive-1-cell-globular-map-is-colaxly-reflexive-globular-map
  ( is-colaxly-reflexive-id-colaxly-reflexive-globular-map G) =
  is-colaxly-reflexive-id-colaxly-reflexive-globular-map
    ( 1-cell-reflexive-globular-type-Reflexive-Globular-Type G _ _)

id-colaxly-reflexive-globular-map :
  {l1 l2 : Level} (G : Reflexive-Globular-Type l1 l2) →
  colaxly-reflexive-globular-map G G
globular-map-colaxly-reflexive-globular-map
  ( id-colaxly-reflexive-globular-map G) =
  map-id-colaxly-reflexive-globular-map G
is-colaxly-reflexive-colaxly-reflexive-globular-map
  ( id-colaxly-reflexive-globular-map G) =
  ( is-colaxly-reflexive-id-colaxly-reflexive-globular-map G)
```

## See also

- [Laxly reflexive globular maps](structured-types.laxly-reflexive-globular-maps.md)
- [Reflexive globular maps](structured-types.reflexive-globular-maps.md)
