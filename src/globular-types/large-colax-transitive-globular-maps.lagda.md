# Large colax transitive globular maps

```agda
{-# OPTIONS --guardedness #-}

open import foundation.function-extensionality-axiom

module
  globular-types.large-colax-transitive-globular-maps
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.function-types funext
open import foundation.universe-levels

open import globular-types.colax-transitive-globular-maps funext
open import globular-types.large-globular-maps funext
open import globular-types.large-transitive-globular-types funext
open import globular-types.transitive-globular-types funext
```

</details>

## Idea

A
{{#concept "large colax transitive globular map" Agda=large-colax-transitive-globular-map}}
between two
[large transitive globular types](globular-types.large-transitive-globular-types.md)
`G` and `H` is a [large globular map](globular-types.large-globular-maps.md)
`f : G → H` equipped with a family of 2-cells

```text
  H₂ (f₁ (q ∘G p)) (f₁ q ∘H f₁ p)
```

from the image of the composite of two 1-cells `q` and `p` in `G` to the
composite of `f₁ q` and `f₁ p` in `H`, such that the globular map
`f' : G' x y → H' (f₀ x) (f₀ y)` is again colax transitive.

### Lack of identity large colax transitive globular maps

Note that the large colax transitive globular maps lack an identity morphism.
For an identity morphism to exist on a transitive globular type `G`, there
should be a `2`-cell from `q ∘G p` to `q ∘G p` for every composable pair of
`1`-cells `q` and `p`. However, since the large transitive globular type `G` is
not assumed to be [reflexive](globular-types.large-reflexive-globular-types.md),
it might lack such instances of the reflexivity cells.

## Definitions

### The predicate of colaxly preserving transitivity

```agda
record
  is-colax-transitive-large-globular-map
    {α1 α2 : Level → Level} {β1 β2 : Level → Level → Level} {γ : Level → Level}
    (G : Large-Transitive-Globular-Type α1 β1)
    (H : Large-Transitive-Globular-Type α2 β2)
    (f : large-globular-map-Large-Transitive-Globular-Type γ G H) : UUω
  where

  field
    preserves-comp-1-cell-is-colax-transitive-large-globular-map :
      {l1 l2 l3 : Level}
      {x : 0-cell-Large-Transitive-Globular-Type G l1}
      {y : 0-cell-Large-Transitive-Globular-Type G l2}
      {z : 0-cell-Large-Transitive-Globular-Type G l3} →
      (q : 1-cell-Large-Transitive-Globular-Type G y z)
      (p : 1-cell-Large-Transitive-Globular-Type G x y) →
      2-cell-Large-Transitive-Globular-Type H
        ( 1-cell-large-globular-map f
          ( comp-1-cell-Large-Transitive-Globular-Type G q p))
        ( comp-1-cell-Large-Transitive-Globular-Type H
          ( 1-cell-large-globular-map f q)
          ( 1-cell-large-globular-map f p))

  field
    is-colax-transitive-1-cell-globular-map-is-colax-transitive-large-globular-map :
      {l1 l2 : Level}
      {x : 0-cell-Large-Transitive-Globular-Type G l1}
      {y : 0-cell-Large-Transitive-Globular-Type G l2} →
      is-colax-transitive-globular-map
        ( 1-cell-transitive-globular-type-Large-Transitive-Globular-Type G x y)
        ( 1-cell-transitive-globular-type-Large-Transitive-Globular-Type H _ _)
        ( 1-cell-globular-map-large-globular-map f)

open is-colax-transitive-large-globular-map public
```

### Colax transitive globular maps

```agda
record
  large-colax-transitive-globular-map
    {α1 α2 : Level → Level} {β1 β2 : Level → Level → Level} (γ : Level → Level)
    (G : Large-Transitive-Globular-Type α1 β1)
    (H : Large-Transitive-Globular-Type α2 β2) : UUω
  where

  field
    large-globular-map-large-colax-transitive-globular-map :
      large-globular-map-Large-Transitive-Globular-Type γ G H

  0-cell-large-colax-transitive-globular-map :
    {l1 : Level} →
    0-cell-Large-Transitive-Globular-Type G l1 →
    0-cell-Large-Transitive-Globular-Type H (γ l1)
  0-cell-large-colax-transitive-globular-map =
    0-cell-large-globular-map
      large-globular-map-large-colax-transitive-globular-map

  1-cell-large-colax-transitive-globular-map :
    {l1 l2 : Level}
    {x : 0-cell-Large-Transitive-Globular-Type G l1}
    {y : 0-cell-Large-Transitive-Globular-Type G l2} →
    1-cell-Large-Transitive-Globular-Type G x y →
    1-cell-Large-Transitive-Globular-Type H
      ( 0-cell-large-colax-transitive-globular-map x)
      ( 0-cell-large-colax-transitive-globular-map y)
  1-cell-large-colax-transitive-globular-map =
    1-cell-large-globular-map
      large-globular-map-large-colax-transitive-globular-map

  1-cell-globular-map-large-colax-transitive-globular-map :
    {l1 l2 : Level}
    {x : 0-cell-Large-Transitive-Globular-Type G l1}
    {y : 0-cell-Large-Transitive-Globular-Type G l2} →
    globular-map-Transitive-Globular-Type
      ( 1-cell-transitive-globular-type-Large-Transitive-Globular-Type G x y)
      ( 1-cell-transitive-globular-type-Large-Transitive-Globular-Type H
        ( 0-cell-large-colax-transitive-globular-map x)
        ( 0-cell-large-colax-transitive-globular-map y))
  1-cell-globular-map-large-colax-transitive-globular-map =
    1-cell-globular-map-large-globular-map
      large-globular-map-large-colax-transitive-globular-map

  2-cell-large-colax-transitive-globular-map :
    {l1 l2 : Level}
    {x : 0-cell-Large-Transitive-Globular-Type G l1}
    {y : 0-cell-Large-Transitive-Globular-Type G l2} →
    {f g : 1-cell-Large-Transitive-Globular-Type G x y} →
    2-cell-Large-Transitive-Globular-Type G f g →
    2-cell-Large-Transitive-Globular-Type H
      ( 1-cell-large-colax-transitive-globular-map f)
      ( 1-cell-large-colax-transitive-globular-map g)
  2-cell-large-colax-transitive-globular-map =
    2-cell-large-globular-map
      large-globular-map-large-colax-transitive-globular-map

  2-cell-globular-map-large-colax-transitive-globular-map :
    {l1 l2 : Level}
    {x : 0-cell-Large-Transitive-Globular-Type G l1}
    {y : 0-cell-Large-Transitive-Globular-Type G l2} →
    {f g : 1-cell-Large-Transitive-Globular-Type G x y} →
    globular-map-Transitive-Globular-Type
      ( 2-cell-transitive-globular-type-Large-Transitive-Globular-Type G f g)
      ( 2-cell-transitive-globular-type-Large-Transitive-Globular-Type H
        ( 1-cell-large-colax-transitive-globular-map f)
        ( 1-cell-large-colax-transitive-globular-map g))
  2-cell-globular-map-large-colax-transitive-globular-map =
    2-cell-globular-map-large-globular-map
      ( large-globular-map-large-colax-transitive-globular-map)
      ( _)
      ( _)

  field
    is-colax-transitive-large-colax-transitive-globular-map :
      is-colax-transitive-large-globular-map G H
        large-globular-map-large-colax-transitive-globular-map

  preserves-comp-1-cell-large-colax-transitive-globular-map :
    {l1 l2 l3 : Level}
    {x : 0-cell-Large-Transitive-Globular-Type G l1}
    {y : 0-cell-Large-Transitive-Globular-Type G l2}
    {z : 0-cell-Large-Transitive-Globular-Type G l3}
    (q : 1-cell-Large-Transitive-Globular-Type G y z)
    (p : 1-cell-Large-Transitive-Globular-Type G x y) →
    2-cell-Large-Transitive-Globular-Type H
      ( 1-cell-large-colax-transitive-globular-map
        ( comp-1-cell-Large-Transitive-Globular-Type G q p))
      ( comp-1-cell-Large-Transitive-Globular-Type H
        ( 1-cell-large-colax-transitive-globular-map q)
        ( 1-cell-large-colax-transitive-globular-map p))
  preserves-comp-1-cell-large-colax-transitive-globular-map =
    preserves-comp-1-cell-is-colax-transitive-large-globular-map
      is-colax-transitive-large-colax-transitive-globular-map

  is-colax-transitive-1-cell-globular-map-large-colax-transitive-globular-map :
    {l1 l2 : Level}
    {x : 0-cell-Large-Transitive-Globular-Type G l1}
    {y : 0-cell-Large-Transitive-Globular-Type G l2} →
    is-colax-transitive-globular-map
      ( 1-cell-transitive-globular-type-Large-Transitive-Globular-Type G x y)
      ( 1-cell-transitive-globular-type-Large-Transitive-Globular-Type H
        ( 0-cell-large-colax-transitive-globular-map x)
        ( 0-cell-large-colax-transitive-globular-map y))
      ( 1-cell-globular-map-large-colax-transitive-globular-map)
  is-colax-transitive-1-cell-globular-map-large-colax-transitive-globular-map =
    is-colax-transitive-1-cell-globular-map-is-colax-transitive-large-globular-map
      is-colax-transitive-large-colax-transitive-globular-map

  1-cell-large-colax-transitive-large-globular-map-large-colax-transitive-globular-map :
    {l1 l2 : Level}
    {x : 0-cell-Large-Transitive-Globular-Type G l1}
    {y : 0-cell-Large-Transitive-Globular-Type G l2} →
    colax-transitive-globular-map
      ( 1-cell-transitive-globular-type-Large-Transitive-Globular-Type G x y)
      ( 1-cell-transitive-globular-type-Large-Transitive-Globular-Type H
        ( 0-cell-large-colax-transitive-globular-map x)
        ( 0-cell-large-colax-transitive-globular-map y))
  globular-map-colax-transitive-globular-map
    1-cell-large-colax-transitive-large-globular-map-large-colax-transitive-globular-map =
    1-cell-globular-map-large-colax-transitive-globular-map
  is-colax-transitive-colax-transitive-globular-map
    1-cell-large-colax-transitive-large-globular-map-large-colax-transitive-globular-map =
    is-colax-transitive-1-cell-globular-map-large-colax-transitive-globular-map

open large-colax-transitive-globular-map public
```

### Composition of colax transitive maps

```agda
map-comp-large-colax-transitive-globular-map :
  {α1 α2 α3 γ1 γ2 : Level → Level} {β1 β2 β3 : Level → Level → Level}
  (G : Large-Transitive-Globular-Type α1 β1)
  (H : Large-Transitive-Globular-Type α2 β2)
  (K : Large-Transitive-Globular-Type α3 β3)
  (g : large-colax-transitive-globular-map γ2 H K)
  (f : large-colax-transitive-globular-map γ1 G H) →
  large-globular-map-Large-Transitive-Globular-Type (γ2 ∘ γ1) G K
map-comp-large-colax-transitive-globular-map G H K g f =
  comp-large-globular-map
    ( large-globular-map-large-colax-transitive-globular-map g)
    ( large-globular-map-large-colax-transitive-globular-map f)

is-colax-transitive-comp-large-colax-transitive-globular-map :
  {α1 α2 α3 γ1 γ2 : Level → Level} {β1 β2 β3 : Level → Level → Level}
  (G : Large-Transitive-Globular-Type α1 β1)
  (H : Large-Transitive-Globular-Type α2 β2)
  (K : Large-Transitive-Globular-Type α3 β3)
  (g : large-colax-transitive-globular-map γ2 H K)
  (f : large-colax-transitive-globular-map γ1 G H) →
  is-colax-transitive-large-globular-map G K
    ( map-comp-large-colax-transitive-globular-map G H K g f)
preserves-comp-1-cell-is-colax-transitive-large-globular-map
  ( is-colax-transitive-comp-large-colax-transitive-globular-map G H K g f)
  ( q)
  ( p) =
  comp-2-cell-Large-Transitive-Globular-Type K
    ( preserves-comp-1-cell-large-colax-transitive-globular-map g _ _)
    ( 2-cell-large-colax-transitive-globular-map g
      ( preserves-comp-1-cell-large-colax-transitive-globular-map f q p))
is-colax-transitive-1-cell-globular-map-is-colax-transitive-large-globular-map
  ( is-colax-transitive-comp-large-colax-transitive-globular-map
    G H K g f) =
  is-colax-transitive-comp-colax-transitive-globular-map
    ( 1-cell-transitive-globular-type-Large-Transitive-Globular-Type G _ _)
    ( 1-cell-transitive-globular-type-Large-Transitive-Globular-Type H _ _)
    ( 1-cell-transitive-globular-type-Large-Transitive-Globular-Type K _ _)
    ( 1-cell-large-colax-transitive-large-globular-map-large-colax-transitive-globular-map
      g)
    ( 1-cell-large-colax-transitive-large-globular-map-large-colax-transitive-globular-map
      f)
```
