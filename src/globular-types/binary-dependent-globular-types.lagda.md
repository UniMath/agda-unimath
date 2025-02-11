# Binary dependent globular types

```agda
{-# OPTIONS --guardedness #-}

module globular-types.binary-dependent-globular-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import globular-types.globular-types
open import globular-types.points-globular-types
```

</details>

## Idea

Consider two [globular types](globular-types.globular-types.md) `G` and `H`. A
{{#concept "binary dependent globular type" Agda=Binary-Dependent-Globular-Type}}
`K` over `G` and `H` consists of

```text
  K₀ : G₀ → H₀ → Type
  K' : (x x' : G₀) (y y' : H₀) →
       K₀ x y → K₀ y y' → Binary-Dependent-Globular-Type (G' x x') (H' y y').
```

## Definitions

### Binary dependent globular types

```agda
record
  Binary-Dependent-Globular-Type
    {l1 l2 l3 l4 : Level} (l5 l6 : Level)
    (G : Globular-Type l1 l2) (H : Globular-Type l3 l4) :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ lsuc l5 ⊔ lsuc l6)
  where
  coinductive

  field
    0-cell-Binary-Dependent-Globular-Type :
      0-cell-Globular-Type G → 0-cell-Globular-Type H → UU l5

  field
    1-cell-binary-dependent-globular-type-Binary-Dependent-Globular-Type :
      {x x' : 0-cell-Globular-Type G} {y y' : 0-cell-Globular-Type H} →
      0-cell-Binary-Dependent-Globular-Type x y →
      0-cell-Binary-Dependent-Globular-Type x' y' →
      Binary-Dependent-Globular-Type l6 l6
        ( 1-cell-globular-type-Globular-Type G x x')
        ( 1-cell-globular-type-Globular-Type H y y')

open Binary-Dependent-Globular-Type public

module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {G : Globular-Type l1 l2} {H : Globular-Type l3 l4}
  (K : Binary-Dependent-Globular-Type l5 l6 G H)
  where

  1-cell-Binary-Dependent-Globular-Type :
    {x x' : 0-cell-Globular-Type G} {y y' : 0-cell-Globular-Type H} →
    0-cell-Binary-Dependent-Globular-Type K x y →
    0-cell-Binary-Dependent-Globular-Type K x' y' →
    1-cell-Globular-Type G x x' →
    1-cell-Globular-Type H y y' → UU l6
  1-cell-Binary-Dependent-Globular-Type u v =
    0-cell-Binary-Dependent-Globular-Type
      ( 1-cell-binary-dependent-globular-type-Binary-Dependent-Globular-Type K
        u v)
```

### Evaluating binary dependent globular types at a pair of points

```agda
ev-point-Binary-Dependent-Globular-Type :
  {l1 l2 l3 l4 l5 l6 : Level}
  {G : Globular-Type l1 l2} {H : Globular-Type l3 l4}
  (K : Binary-Dependent-Globular-Type l5 l6 G H)
  (x : point-Globular-Type G) (y : point-Globular-Type H) →
  Globular-Type l5 l6
0-cell-Globular-Type (ev-point-Binary-Dependent-Globular-Type K x y) =
  0-cell-Binary-Dependent-Globular-Type K
    ( 0-cell-point-Globular-Type x)
    ( 0-cell-point-Globular-Type y)
1-cell-globular-type-Globular-Type
  ( ev-point-Binary-Dependent-Globular-Type K x y) u v =
  ev-point-Binary-Dependent-Globular-Type
    ( 1-cell-binary-dependent-globular-type-Binary-Dependent-Globular-Type
      K u v)
    ( 1-cell-point-point-Globular-Type x)
    ( 1-cell-point-point-Globular-Type y)
```
