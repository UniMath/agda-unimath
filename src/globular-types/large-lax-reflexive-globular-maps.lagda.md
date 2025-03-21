# Large lax reflexive globular maps

```agda
{-# OPTIONS --guardedness #-}

module globular-types.large-lax-reflexive-globular-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.function-types
open import foundation.universe-levels

open import globular-types.large-globular-maps
open import globular-types.large-reflexive-globular-types
open import globular-types.lax-reflexive-globular-maps
open import globular-types.reflexive-globular-types
```

</details>

## Idea

A
{{#concept "large lax reflexive globular map" Agda=large-lax-reflexive-globular-map}}
between two
[large reflexive globular types](globular-types.large-reflexive-globular-types.md)
`G` and `H` is a [large globular map](globular-types.large-globular-maps.md)
`f : G → H` equipped with a family of 2-cells

```text
  (x : G₀) → H₂ (refl H (f₀ x)) (f₁ (refl G x))
```

from the image of the reflexivity cell at `x` in `G` to the reflexivity cell at
`f₀ x`, such that the [globular map](globular-types.globular-maps.md)
`f' : G' x y → H' (f₀ x) (f₀ y)` is
[lax reflexive](globular-types.lax-reflexive-globular-maps.md).

### Lack of composition for lax reflexive globular maps

Note that the large lax reflexive globular maps lack composition. For the
composition of `g` and `f` to exist, there should be a `2`-cell from
`g (f (refl G x))` to `refl K (g (f x))`, we need to compose the 2-cell that `g`
preserves reflexivity with the action of `g` on the 2-cell that `f` preserves
reflexivity. However, since the reflexive globular type `G` is not assumed to be
[transitive](globular-types.transitive-globular-types.md), it might lack such
instances of the compositions.

### Lax versus colax

The notion of
[large colax reflexive globular map](globular-types.large-lax-reflexive-globular-maps.md)
is almost the same, except with the direction of the 2-cell reversed. In
general, the direction of lax coherence cells is determined by applying the
morphism componentwise first, and then the operations, while the direction of
colax coherence cells is determined by first applying the operations and then
the morphism.

## Definitions

### The predicate of laxly preserving reflexivity

```agda
record
  is-lax-reflexive-large-globular-map
    {α1 α2 : Level → Level} {β1 β2 : Level → Level → Level} {γ : Level → Level}
    (G : Large-Reflexive-Globular-Type α1 β1)
    (H : Large-Reflexive-Globular-Type α2 β2)
    (f : large-globular-map-Large-Reflexive-Globular-Type γ G H) : UUω
  where

  field
    preserves-refl-1-cell-is-lax-reflexive-large-globular-map :
      {l1 : Level}
      (x : 0-cell-Large-Reflexive-Globular-Type G l1) →
      2-cell-Large-Reflexive-Globular-Type H
        ( refl-1-cell-Large-Reflexive-Globular-Type H)
        ( 1-cell-large-globular-map f
          ( refl-1-cell-Large-Reflexive-Globular-Type G {x = x}))

  field
    is-lax-reflexive-1-cell-globular-map-is-lax-reflexive-large-globular-map :
      {l1 l2 : Level}
      {x : 0-cell-Large-Reflexive-Globular-Type G l1}
      {y : 0-cell-Large-Reflexive-Globular-Type G l2} →
      is-lax-reflexive-globular-map
        ( 1-cell-reflexive-globular-type-Large-Reflexive-Globular-Type G x y)
        ( 1-cell-reflexive-globular-type-Large-Reflexive-Globular-Type H _ _)
        ( 1-cell-globular-map-large-globular-map f)

open is-lax-reflexive-large-globular-map public
```

### Lax reflexive globular maps

```agda
record
  large-lax-reflexive-globular-map
    {α1 α2 : Level → Level} {β1 β2 : Level → Level → Level} (γ : Level → Level)
    (G : Large-Reflexive-Globular-Type α1 β1)
    (H : Large-Reflexive-Globular-Type α2 β2) : UUω
  where

  field
    large-globular-map-large-lax-reflexive-globular-map :
      large-globular-map-Large-Reflexive-Globular-Type γ G H

  0-cell-large-lax-reflexive-globular-map :
    {l1 : Level} →
    0-cell-Large-Reflexive-Globular-Type G l1 →
    0-cell-Large-Reflexive-Globular-Type H (γ l1)
  0-cell-large-lax-reflexive-globular-map =
    0-cell-large-globular-map
      large-globular-map-large-lax-reflexive-globular-map

  1-cell-large-lax-reflexive-globular-map :
    {l1 l2 : Level}
    {x : 0-cell-Large-Reflexive-Globular-Type G l1}
    {y : 0-cell-Large-Reflexive-Globular-Type G l2} →
    1-cell-Large-Reflexive-Globular-Type G x y →
    1-cell-Large-Reflexive-Globular-Type H
      ( 0-cell-large-lax-reflexive-globular-map x)
      ( 0-cell-large-lax-reflexive-globular-map y)
  1-cell-large-lax-reflexive-globular-map =
    1-cell-large-globular-map
      large-globular-map-large-lax-reflexive-globular-map

  1-cell-globular-map-large-lax-reflexive-globular-map :
    {l1 l2 : Level}
    {x : 0-cell-Large-Reflexive-Globular-Type G l1}
    {y : 0-cell-Large-Reflexive-Globular-Type G l2} →
    globular-map-Reflexive-Globular-Type
      ( 1-cell-reflexive-globular-type-Large-Reflexive-Globular-Type G x y)
      ( 1-cell-reflexive-globular-type-Large-Reflexive-Globular-Type H
        ( 0-cell-large-lax-reflexive-globular-map x)
        ( 0-cell-large-lax-reflexive-globular-map y))
  1-cell-globular-map-large-lax-reflexive-globular-map =
    1-cell-globular-map-large-globular-map
      large-globular-map-large-lax-reflexive-globular-map

  field
    is-lax-reflexive-large-lax-reflexive-globular-map :
      is-lax-reflexive-large-globular-map G H
        large-globular-map-large-lax-reflexive-globular-map

  preserves-refl-1-cell-large-lax-reflexive-globular-map :
    {l1 : Level}
    (x : 0-cell-Large-Reflexive-Globular-Type G l1) →
    2-cell-Large-Reflexive-Globular-Type H
      ( refl-1-cell-Large-Reflexive-Globular-Type H)
      ( 1-cell-large-lax-reflexive-globular-map
        ( refl-1-cell-Large-Reflexive-Globular-Type G {x = x}))
  preserves-refl-1-cell-large-lax-reflexive-globular-map =
    preserves-refl-1-cell-is-lax-reflexive-large-globular-map
      is-lax-reflexive-large-lax-reflexive-globular-map

  is-lax-reflexive-2-cell-globular-map-is-lax-reflexive-large-globular-map :
    {l1 l2 : Level}
    {x : 0-cell-Large-Reflexive-Globular-Type G l1}
    {y : 0-cell-Large-Reflexive-Globular-Type G l2} →
    is-lax-reflexive-globular-map
      ( 1-cell-reflexive-globular-type-Large-Reflexive-Globular-Type G x y)
      ( 1-cell-reflexive-globular-type-Large-Reflexive-Globular-Type H
        ( 0-cell-large-lax-reflexive-globular-map x)
        ( 0-cell-large-lax-reflexive-globular-map y))
      ( 1-cell-globular-map-large-lax-reflexive-globular-map)
  is-lax-reflexive-2-cell-globular-map-is-lax-reflexive-large-globular-map =
    is-lax-reflexive-1-cell-globular-map-is-lax-reflexive-large-globular-map
      is-lax-reflexive-large-lax-reflexive-globular-map

  1-cell-lax-reflexive-globular-map-large-lax-reflexive-globular-map :
    {l1 l2 : Level}
    {x : 0-cell-Large-Reflexive-Globular-Type G l1}
    {y : 0-cell-Large-Reflexive-Globular-Type G l2} →
    lax-reflexive-globular-map
      ( 1-cell-reflexive-globular-type-Large-Reflexive-Globular-Type G x y)
      ( 1-cell-reflexive-globular-type-Large-Reflexive-Globular-Type H
        ( 0-cell-large-lax-reflexive-globular-map x)
        ( 0-cell-large-lax-reflexive-globular-map y))
  globular-map-lax-reflexive-globular-map
    1-cell-lax-reflexive-globular-map-large-lax-reflexive-globular-map =
    1-cell-globular-map-large-lax-reflexive-globular-map
  is-lax-reflexive-lax-reflexive-globular-map
    1-cell-lax-reflexive-globular-map-large-lax-reflexive-globular-map =
    is-lax-reflexive-2-cell-globular-map-is-lax-reflexive-large-globular-map

open large-lax-reflexive-globular-map public
```

### The identity large lax reflexive globular map

```agda
map-id-large-lax-reflexive-globular-map :
  {α : Level → Level} {β : Level → Level → Level}
  (G : Large-Reflexive-Globular-Type α β) →
  large-globular-map-Large-Reflexive-Globular-Type id G G
map-id-large-lax-reflexive-globular-map G = id-large-globular-map _

is-lax-reflexive-id-large-lax-reflexive-globular-map :
  {α : Level → Level} {β : Level → Level → Level}
  (G : Large-Reflexive-Globular-Type α β) →
  is-lax-reflexive-large-globular-map G G
    ( map-id-large-lax-reflexive-globular-map G)
preserves-refl-1-cell-is-lax-reflexive-large-globular-map
  ( is-lax-reflexive-id-large-lax-reflexive-globular-map G)
  x =
  refl-2-cell-Large-Reflexive-Globular-Type G
is-lax-reflexive-1-cell-globular-map-is-lax-reflexive-large-globular-map
  ( is-lax-reflexive-id-large-lax-reflexive-globular-map G) =
  is-lax-reflexive-id-lax-reflexive-globular-map
    ( 1-cell-reflexive-globular-type-Large-Reflexive-Globular-Type G _ _)

id-large-lax-reflexive-globular-map :
  {α : Level → Level} {β : Level → Level → Level}
  (G : Large-Reflexive-Globular-Type α β) →
  large-lax-reflexive-globular-map id G G
large-globular-map-large-lax-reflexive-globular-map
  ( id-large-lax-reflexive-globular-map G) =
  map-id-large-lax-reflexive-globular-map G
is-lax-reflexive-large-lax-reflexive-globular-map
  ( id-large-lax-reflexive-globular-map G) =
  ( is-lax-reflexive-id-large-lax-reflexive-globular-map G)
```

## See also

- [Lax reflexive globular maps](globular-types.lax-reflexive-globular-maps.md)
- [Reflexive globular maps](globular-types.reflexive-globular-maps.md)
