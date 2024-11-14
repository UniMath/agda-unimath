# Points of reflexive globular types

```agda
{-# OPTIONS --guardedness #-}

module structured-types.points-reflexive-globular-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import structured-types.points-globular-types
open import structured-types.reflexive-globular-types
```

</details>

## Idea

Consider a
[reflexive globular type](structured-types.reflexive-globular-types.md) `G`. A
{{#concept "point" Disambiguation="reflexive globular type" Agda=point-Reflexive-Globular-Type}}
of `G` is a 0-cell of `G`. Equivalently, a point of `G` is a
[reflexive globular map](structured-types.reflexive-globular-maps.md) from the
[unit reflexive globular type](structured-types.unit-reflexive-globular-type.md)
into `G`.

The definition of points of reflexive globular types is much simpler than the
definition of [points](structured-types.points-globular-types.md) of ordinary
[globular types](structured-types.globular-types.md). This is due to the
condition that reflexive globular maps preserve reflexivity, and therefore the
type of higher cells relating the underlying 0-cell to itself is
[contractible](foundation-core.contractible-types.md).

## Definitions

### Points of reflexive globular types

```agda
module _
  {l1 l2 : Level} (G : Reflexive-Globular-Type l1 l2)
  where

  point-Reflexive-Globular-Type : UU l1
  point-Reflexive-Globular-Type = 0-cell-Reflexive-Globular-Type G
```

### The underlying points of the underlying globular type of a reflexive globular type

```agda
point-globular-type-point-Reflexive-Globular-Type :
  {l1 l2 : Level} (G : Reflexive-Globular-Type l1 l2) →
  point-Reflexive-Globular-Type G →
  point-Globular-Type (globular-type-Reflexive-Globular-Type G)
0-cell-point-Globular-Type
  ( point-globular-type-point-Reflexive-Globular-Type G x) =
  x
1-cell-point-point-Globular-Type
  ( point-globular-type-point-Reflexive-Globular-Type G x) =
  point-globular-type-point-Reflexive-Globular-Type
    ( 1-cell-reflexive-globular-type-Reflexive-Globular-Type G x x)
    ( refl-1-cell-Reflexive-Globular-Type G)
```
