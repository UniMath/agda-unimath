# Colax reflexive globular maps

```agda
{-# OPTIONS --guardedness #-}

module globular-types.colax-reflexive-globular-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import globular-types.globular-maps
open import globular-types.reflexive-globular-types
```

</details>

## Idea

A {{#concept "colax reflexive globular map" Agda=colax-reflexive-globular-map}}
between two
[reflexive globular types](globular-types.reflexive-globular-types.md) `G` and
`H` is a [globular map](globular-types.globular-maps.md) `f : G → H` equipped
with a family of 2-cells

```text
  (x : G₀) → H₂ (f₁ (refl G x)) (refl H (f₀ x))
```

from the image of the reflexivity cell at `x` in `G` to the reflexivity cell at
`f₀ x`, such that the globular map `f' : G' x y → H' (f₀ x) (f₀ y)` is again
colax reflexive.

### Lack of composition for colax reflexive globular maps

Note that the colax reflexive globular maps lack composition. For the
composition of `g` and `f` to exist, there should be a `2`-cell from
`g (f (refl G x))` to `refl K (g (f x))`, we need to compose the 2-cell that `g`
preserves reflexivity with the action of `g` on the 2-cell that `f` preserves
reflexivity. However, since the reflexive globular type `G` is not assumed to be
[transitive](globular-types.transitive-globular-types.md), it might lack such
instances of the compositions.

### Colax reflexive globular maps versus the morphisms of presheaves on the reflexive globe category

When reflexive globular types are viewed as type valued presheaves over the
reflexive globe category, the resulting notion of morphism is that of
[reflexive globular maps](globular-types.reflexive-globular-maps.md), which is
stricter than the notion of colax reflexive globular maps.

### Lax versus colax

The notion of
[lax reflexive globular map](globular-types.lax-reflexive-globular-maps.md) is
almost the same, except with the direction of the 2-cell reversed. In general,
the direction of lax coherence cells is determined by applying the morphism
componentwise first, and then the operations, while the direction of colax
coherence cells is determined by first applying the operations and then the
morphism.

## Definitions

### The predicate of colaxly preserving reflexivity

```agda
record
  is-colax-reflexive-globular-map
    {l1 l2 l3 l4 : Level}
    (G : Reflexive-Globular-Type l1 l2) (H : Reflexive-Globular-Type l3 l4)
    (f : globular-map-Reflexive-Globular-Type G H) :
    UU (l1 ⊔ l2 ⊔ l4)
  where
  coinductive

  field
    preserves-refl-1-cell-is-colax-reflexive-globular-map :
      (x : 0-cell-Reflexive-Globular-Type G) →
      2-cell-Reflexive-Globular-Type H
        ( 1-cell-globular-map f (refl-1-cell-Reflexive-Globular-Type G {x}))
        ( refl-1-cell-Reflexive-Globular-Type H)

  field
    is-colax-reflexive-1-cell-globular-map-is-colax-reflexive-globular-map :
      {x y : 0-cell-Reflexive-Globular-Type G} →
      is-colax-reflexive-globular-map
        ( 1-cell-reflexive-globular-type-Reflexive-Globular-Type G x y)
        ( 1-cell-reflexive-globular-type-Reflexive-Globular-Type H _ _)
        ( 1-cell-globular-map-globular-map-Reflexive-Globular-Type G H f)

open is-colax-reflexive-globular-map public
```

### Colax reflexive globular maps

```agda
record
  colax-reflexive-globular-map
    {l1 l2 l3 l4 : Level}
    (G : Reflexive-Globular-Type l1 l2)
    (H : Reflexive-Globular-Type l3 l4) :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  where

  constructor
    make-colax-reflexive-globular-map

  field
    globular-map-colax-reflexive-globular-map :
      globular-map-Reflexive-Globular-Type G H

  0-cell-colax-reflexive-globular-map :
    0-cell-Reflexive-Globular-Type G → 0-cell-Reflexive-Globular-Type H
  0-cell-colax-reflexive-globular-map =
    0-cell-globular-map globular-map-colax-reflexive-globular-map

  1-cell-colax-reflexive-globular-map :
    {x y : 0-cell-Reflexive-Globular-Type G} →
    1-cell-Reflexive-Globular-Type G x y →
    1-cell-Reflexive-Globular-Type H
      ( 0-cell-colax-reflexive-globular-map x)
      ( 0-cell-colax-reflexive-globular-map y)
  1-cell-colax-reflexive-globular-map =
    1-cell-globular-map globular-map-colax-reflexive-globular-map

  1-cell-globular-map-colax-reflexive-globular-map :
    {x y : 0-cell-Reflexive-Globular-Type G} →
    globular-map-Reflexive-Globular-Type
      ( 1-cell-reflexive-globular-type-Reflexive-Globular-Type G x y)
      ( 1-cell-reflexive-globular-type-Reflexive-Globular-Type H
        ( 0-cell-colax-reflexive-globular-map x)
        ( 0-cell-colax-reflexive-globular-map y))
  1-cell-globular-map-colax-reflexive-globular-map =
    1-cell-globular-map-globular-map globular-map-colax-reflexive-globular-map

  field
    is-colax-reflexive-colax-reflexive-globular-map :
      is-colax-reflexive-globular-map G H
        globular-map-colax-reflexive-globular-map

  preserves-refl-1-cell-colax-reflexive-globular-map :
    ( x : 0-cell-Reflexive-Globular-Type G) →
    2-cell-Reflexive-Globular-Type H
      ( 1-cell-colax-reflexive-globular-map
        ( refl-1-cell-Reflexive-Globular-Type G {x}))
      ( refl-1-cell-Reflexive-Globular-Type H)
  preserves-refl-1-cell-colax-reflexive-globular-map =
    preserves-refl-1-cell-is-colax-reflexive-globular-map
      is-colax-reflexive-colax-reflexive-globular-map

  is-colax-reflexive-2-cell-globular-map-is-colax-reflexive-globular-map :
    { x y : 0-cell-Reflexive-Globular-Type G} →
    is-colax-reflexive-globular-map
      ( 1-cell-reflexive-globular-type-Reflexive-Globular-Type G x y)
      ( 1-cell-reflexive-globular-type-Reflexive-Globular-Type H
        ( 0-cell-colax-reflexive-globular-map x)
        ( 0-cell-colax-reflexive-globular-map y))
      ( 1-cell-globular-map-colax-reflexive-globular-map)
  is-colax-reflexive-2-cell-globular-map-is-colax-reflexive-globular-map =
    is-colax-reflexive-1-cell-globular-map-is-colax-reflexive-globular-map
      is-colax-reflexive-colax-reflexive-globular-map

  1-cell-colax-reflexive-globular-map-colax-reflexive-globular-map :
    {x y : 0-cell-Reflexive-Globular-Type G} →
    colax-reflexive-globular-map
      ( 1-cell-reflexive-globular-type-Reflexive-Globular-Type G x y)
      ( 1-cell-reflexive-globular-type-Reflexive-Globular-Type H
        ( 0-cell-colax-reflexive-globular-map x)
        ( 0-cell-colax-reflexive-globular-map y))
  globular-map-colax-reflexive-globular-map
    1-cell-colax-reflexive-globular-map-colax-reflexive-globular-map =
    1-cell-globular-map-colax-reflexive-globular-map
  is-colax-reflexive-colax-reflexive-globular-map
    1-cell-colax-reflexive-globular-map-colax-reflexive-globular-map =
    is-colax-reflexive-2-cell-globular-map-is-colax-reflexive-globular-map

open colax-reflexive-globular-map public
```

### The identity colax reflexive globular map

```agda
map-id-colax-reflexive-globular-map :
  {l1 l2 : Level} (G : Reflexive-Globular-Type l1 l2) →
  globular-map-Reflexive-Globular-Type G G
map-id-colax-reflexive-globular-map G = id-globular-map _

is-colax-reflexive-id-colax-reflexive-globular-map :
  {l1 l2 : Level} (G : Reflexive-Globular-Type l1 l2) →
  is-colax-reflexive-globular-map G G
    ( map-id-colax-reflexive-globular-map G)
preserves-refl-1-cell-is-colax-reflexive-globular-map
  ( is-colax-reflexive-id-colax-reflexive-globular-map G)
  x =
  refl-2-cell-Reflexive-Globular-Type G
is-colax-reflexive-1-cell-globular-map-is-colax-reflexive-globular-map
  ( is-colax-reflexive-id-colax-reflexive-globular-map G) =
  is-colax-reflexive-id-colax-reflexive-globular-map
    ( 1-cell-reflexive-globular-type-Reflexive-Globular-Type G _ _)

id-colax-reflexive-globular-map :
  {l1 l2 : Level} (G : Reflexive-Globular-Type l1 l2) →
  colax-reflexive-globular-map G G
globular-map-colax-reflexive-globular-map
  ( id-colax-reflexive-globular-map G) =
  map-id-colax-reflexive-globular-map G
is-colax-reflexive-colax-reflexive-globular-map
  ( id-colax-reflexive-globular-map G) =
  ( is-colax-reflexive-id-colax-reflexive-globular-map G)
```

## See also

- [Lax reflexive globular maps](globular-types.lax-reflexive-globular-maps.md)
- [Reflexive globular maps](globular-types.reflexive-globular-maps.md)
