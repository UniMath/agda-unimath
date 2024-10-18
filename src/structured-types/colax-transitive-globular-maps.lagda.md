# Colax transitive globular maps

```agda
{-# OPTIONS --guardedness #-}

module structured-types.colax-transitive-globular-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import structured-types.globular-maps
open import structured-types.transitive-globular-types
```

</details>

## Idea

A {{#concept "colax transitive globular map" Agda=transitive-globular-map}} between
two [transitive globular types](structured-types.transitive-globular-types.md) `G`
and `H` is a [globular map](structured-types.globular-maps.md) `f : G → H`
equipped with a family of 2-cells

```text
  H₂ (f₁ (q ∘G p)) (f₁ q ∘H f₁ p)
```

from the image of the composite of two 1-cells `q` and `p` in `G` to the composite of `f₁ q` and `f₁ p` in `H`, such that the globular map `f' : G' x y → H' (f₀ x) (f₀ y)` is again colax
transitive.

## Definitions

### The predicate of colax preserving transitivity

```agda
record
  is-colax-transitive-globular-map
    {l1 l2 l3 l4 : Level}
    (G : Transitive-Globular-Type l1 l2) (H : Transitive-Globular-Type l3 l4)
    (f : globular-map-Transitive-Globular-Type G H) :
    UU (l1 ⊔ l2 ⊔ l4)
  where
  coinductive

  field
    preserves-comp-1-cell-is-colax-transitive-globular-map :
      {x y z : 0-cell-Transitive-Globular-Type G} →
      (q : 1-cell-Transitive-Globular-Type G y z)
      (p : 1-cell-Transitive-Globular-Type G x y) →
      2-cell-Transitive-Globular-Type H
        ( 1-cell-globular-map f
          ( comp-1-cell-Transitive-Globular-Type G q p))
        ( comp-1-cell-Transitive-Globular-Type H
          ( 1-cell-globular-map f q)
          ( 1-cell-globular-map f p))

  field
    is-colax-transitive-1-cell-globular-map-is-colax-transitive-globular-map :
      {x y : 0-cell-Transitive-Globular-Type G} →
      is-colax-transitive-globular-map
        ( 1-cell-transitive-globular-type-Transitive-Globular-Type G x y)
        ( 1-cell-transitive-globular-type-Transitive-Globular-Type H _ _)
        ( 1-cell-globular-map-globular-map f)

open is-colax-transitive-globular-map public
```

### Colax transitive globular maps

```agda
record
  colax-transitive-globular-map
    {l1 l2 l3 l4 : Level}
    (G : Transitive-Globular-Type l1 l2)
    (H : Transitive-Globular-Type l3 l4) :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  where

  field
    globular-map-colax-transitive-globular-map :
      globular-map-Transitive-Globular-Type G H

  0-cell-colax-transitive-globular-map :
    0-cell-Transitive-Globular-Type G → 0-cell-Transitive-Globular-Type H
  0-cell-colax-transitive-globular-map =
    0-cell-globular-map globular-map-colax-transitive-globular-map

  1-cell-colax-transitive-globular-map :
    {x y : 0-cell-Transitive-Globular-Type G} →
    1-cell-Transitive-Globular-Type G x y →
    1-cell-Transitive-Globular-Type H
      ( 0-cell-colax-transitive-globular-map x)
      ( 0-cell-colax-transitive-globular-map y)
  1-cell-colax-transitive-globular-map =
    1-cell-globular-map globular-map-colax-transitive-globular-map

  1-cell-globular-map-colax-transitive-globular-map :
    {x y : 0-cell-Transitive-Globular-Type G} →
    globular-map-Transitive-Globular-Type
      ( 1-cell-transitive-globular-type-Transitive-Globular-Type G x y)
      ( 1-cell-transitive-globular-type-Transitive-Globular-Type H
        ( 0-cell-colax-transitive-globular-map x)
        ( 0-cell-colax-transitive-globular-map y))
  1-cell-globular-map-colax-transitive-globular-map =
    1-cell-globular-map-globular-map globular-map-colax-transitive-globular-map

  field
    is-colax-transitive-colax-transitive-globular-map :
      is-colax-transitive-globular-map G H
        globular-map-colax-transitive-globular-map

  preserves-comp-1-cell-colax-transitive-globular-map :
    {x y z : 0-cell-Transitive-Globular-Type G}
    (q : 1-cell-Transitive-Globular-Type G y z)
    (p : 1-cell-Transitive-Globular-Type G x y) →
    2-cell-Transitive-Globular-Type H
      ( 1-cell-colax-transitive-globular-map
        ( comp-1-cell-Transitive-Globular-Type G q p))
      ( comp-1-cell-Transitive-Globular-Type H
        ( 1-cell-colax-transitive-globular-map q)
        ( 1-cell-colax-transitive-globular-map p))
  preserves-comp-1-cell-colax-transitive-globular-map =
    preserves-comp-1-cell-is-colax-transitive-globular-map
      is-colax-transitive-colax-transitive-globular-map

  is-colax-transitive-1-cell-globular-map-colax-transitive-globular-map :
    { x y : 0-cell-Transitive-Globular-Type G} →
    is-colax-transitive-globular-map
      ( 1-cell-transitive-globular-type-Transitive-Globular-Type G x y)
      ( 1-cell-transitive-globular-type-Transitive-Globular-Type H
        ( 0-cell-colax-transitive-globular-map x)
        ( 0-cell-colax-transitive-globular-map y))
      ( 1-cell-globular-map-colax-transitive-globular-map)
  is-colax-transitive-1-cell-globular-map-colax-transitive-globular-map =
    is-colax-transitive-1-cell-globular-map-is-colax-transitive-globular-map
      is-colax-transitive-colax-transitive-globular-map

  1-cell-colax-transitive-globular-map-colax-transitive-globular-map :
    {x y : 0-cell-Transitive-Globular-Type G} →
    colax-transitive-globular-map
      ( 1-cell-transitive-globular-type-Transitive-Globular-Type G x y)
      ( 1-cell-transitive-globular-type-Transitive-Globular-Type H
        ( 0-cell-colax-transitive-globular-map x)
        ( 0-cell-colax-transitive-globular-map y))
  globular-map-colax-transitive-globular-map
    1-cell-colax-transitive-globular-map-colax-transitive-globular-map =
    1-cell-globular-map-colax-transitive-globular-map
  is-colax-transitive-colax-transitive-globular-map
    1-cell-colax-transitive-globular-map-colax-transitive-globular-map =
    is-colax-transitive-1-cell-globular-map-colax-transitive-globular-map
```
