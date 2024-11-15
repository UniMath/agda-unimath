# Large reflexive globular maps

```agda
{-# OPTIONS --guardedness #-}

module structured-types.large-reflexive-globular-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-types
open import foundation.universe-levels

open import structured-types.large-globular-maps
open import structured-types.large-reflexive-globular-types
open import structured-types.reflexive-globular-maps
open import structured-types.reflexive-globular-types
```

</details>

## Idea

A {{#concept "large reflexive globular map" Agda=large-reflexive-globular-map}}
between two
[large reflexive globular types](structured-types.large-reflexive-globular-types.md)
`G` and `H` is a [large globular map](structured-types.large-globular-maps.md)
`f : G → H` equipped with a family of
[identifications](foundation-core.identity-types.md)

```text
  (x : G₀) → f₁ (refl G x) ＝ refl H (f₀ x)
```

from the image of the reflexivity cell at `x` in `G` to the reflexivity cell at
`f₀ x`, such that the [globular map](structured-types.globular-maps.md)
`f' : G' x y → H' (f₀ x) (f₀ y)` is
[reflexive](structured-types.reflexive-globular-maps.md).

Note: In some settings it may be preferred to work with large globular maps
preserving reflexivity cells up to a higher cell. The two notions of maps
between reflexive globular types preserving the reflexivity structure up to a
higher cell are, depending of the direction of the coherence cells, the notions
of
[large colax reflexive globular maps](structured-types.large-colax-reflexive-globular-maps.md)
and
[large lax reflexive globular maps](structured-types.large-lax-reflexive-globular-maps.md).

## Definitions

### The predicate of preserving reflexivity

```agda
record
  preserves-refl-large-globular-map
    {α1 α2 : Level → Level} {β1 β2 : Level → Level → Level} {γ : Level → Level}
    (G : Large-Reflexive-Globular-Type α1 β1)
    (H : Large-Reflexive-Globular-Type α2 β2)
    (f : large-globular-map-Large-Reflexive-Globular-Type γ G H) :
    UUω
  where
  coinductive

  field
    preserves-refl-1-cell-preserves-refl-large-globular-map :
      {l1 : Level}
      (x : 0-cell-Large-Reflexive-Globular-Type G l1) →
      1-cell-large-globular-map f
        ( refl-1-cell-Large-Reflexive-Globular-Type G {x = x}) ＝
      refl-1-cell-Large-Reflexive-Globular-Type H

  field
    preserves-refl-2-cell-globular-map-preserves-refl-large-globular-map :
      {l1 l2 : Level}
      {x : 0-cell-Large-Reflexive-Globular-Type G l1}
      {y : 0-cell-Large-Reflexive-Globular-Type G l2} →
      preserves-refl-globular-map
        ( 1-cell-reflexive-globular-type-Large-Reflexive-Globular-Type G x y)
        ( 1-cell-reflexive-globular-type-Large-Reflexive-Globular-Type H _ _)
        ( 1-cell-globular-map-large-globular-map f)

open preserves-refl-large-globular-map
```

### Large reflexive globular maps

```agda
record
  large-reflexive-globular-map
    {α1 α2 : Level → Level} {β1 β2 : Level → Level → Level} (γ : Level → Level)
    (G : Large-Reflexive-Globular-Type α1 β1)
    (H : Large-Reflexive-Globular-Type α2 β2) : UUω
  where

  field
    large-globular-map-large-reflexive-globular-map :
      large-globular-map-Large-Reflexive-Globular-Type γ G H

  0-cell-large-reflexive-globular-map :
    {l1 : Level} →
    0-cell-Large-Reflexive-Globular-Type G l1 →
    0-cell-Large-Reflexive-Globular-Type H (γ l1)
  0-cell-large-reflexive-globular-map =
    0-cell-large-globular-map large-globular-map-large-reflexive-globular-map

  1-cell-large-reflexive-globular-map :
    {l1 l2 : Level}
    {x : 0-cell-Large-Reflexive-Globular-Type G l1}
    {y : 0-cell-Large-Reflexive-Globular-Type G l2} →
    1-cell-Large-Reflexive-Globular-Type G x y →
    1-cell-Large-Reflexive-Globular-Type H
      ( 0-cell-large-reflexive-globular-map x)
      ( 0-cell-large-reflexive-globular-map y)
  1-cell-large-reflexive-globular-map =
    1-cell-large-globular-map large-globular-map-large-reflexive-globular-map

  1-cell-globular-map-large-reflexive-globular-map :
    {l1 l2 : Level}
    {x : 0-cell-Large-Reflexive-Globular-Type G l1}
    {y : 0-cell-Large-Reflexive-Globular-Type G l2} →
    globular-map-Reflexive-Globular-Type
      ( 1-cell-reflexive-globular-type-Large-Reflexive-Globular-Type G x y)
      ( 1-cell-reflexive-globular-type-Large-Reflexive-Globular-Type H
        ( 0-cell-large-reflexive-globular-map x)
        ( 0-cell-large-reflexive-globular-map y))
  1-cell-globular-map-large-reflexive-globular-map =
    1-cell-globular-map-large-globular-map
      large-globular-map-large-reflexive-globular-map

  field
    preserves-refl-large-reflexive-globular-map :
      preserves-refl-large-globular-map G H
        large-globular-map-large-reflexive-globular-map

  preserves-refl-1-cell-large-reflexive-globular-map :
    {l1 : Level} (x : 0-cell-Large-Reflexive-Globular-Type G l1) →
    1-cell-large-reflexive-globular-map
      ( refl-1-cell-Large-Reflexive-Globular-Type G {x = x}) ＝
    refl-1-cell-Large-Reflexive-Globular-Type H
  preserves-refl-1-cell-large-reflexive-globular-map =
    preserves-refl-1-cell-preserves-refl-large-globular-map
      preserves-refl-large-reflexive-globular-map

  preserves-refl-2-cell-globular-map-large-reflexive-globular-map :
    {l1 l2 : Level}
    {x : 0-cell-Large-Reflexive-Globular-Type G l1}
    {y : 0-cell-Large-Reflexive-Globular-Type G l2} →
    preserves-refl-globular-map
      ( 1-cell-reflexive-globular-type-Large-Reflexive-Globular-Type G x y)
      ( 1-cell-reflexive-globular-type-Large-Reflexive-Globular-Type H
        ( 0-cell-large-reflexive-globular-map x)
        ( 0-cell-large-reflexive-globular-map y))
      ( 1-cell-globular-map-large-reflexive-globular-map)
  preserves-refl-2-cell-globular-map-large-reflexive-globular-map =
    preserves-refl-2-cell-globular-map-preserves-refl-large-globular-map
      preserves-refl-large-reflexive-globular-map

  1-cell-reflexive-globular-map-large-reflexive-globular-map :
    {l1 l2 : Level}
    {x : 0-cell-Large-Reflexive-Globular-Type G l1}
    {y : 0-cell-Large-Reflexive-Globular-Type G l2} →
    reflexive-globular-map
      ( 1-cell-reflexive-globular-type-Large-Reflexive-Globular-Type G x y)
      ( 1-cell-reflexive-globular-type-Large-Reflexive-Globular-Type H
        ( 0-cell-large-reflexive-globular-map x)
        ( 0-cell-large-reflexive-globular-map y))
  globular-map-reflexive-globular-map
    1-cell-reflexive-globular-map-large-reflexive-globular-map =
    1-cell-globular-map-large-reflexive-globular-map
  preserves-refl-reflexive-globular-map
    1-cell-reflexive-globular-map-large-reflexive-globular-map =
    preserves-refl-2-cell-globular-map-large-reflexive-globular-map

open large-reflexive-globular-map public
```
