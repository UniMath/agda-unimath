# Base change of dependent reflexive globular types

```agda
{-# OPTIONS --guardedness #-}

module structured-types.base-change-dependent-reflexive-globular-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import structured-types.base-change-dependent-globular-types
open import structured-types.dependent-globular-types
open import structured-types.dependent-reflexive-globular-types
open import structured-types.globular-types
open import structured-types.reflexive-globular-maps
open import structured-types.reflexive-globular-types
```

</details>

## Idea

Consider a [reflexive globular map](structured-types.reflexive-globular-maps.md)
`f : G → H` between
[reflexive globular types](structured-types.reflexive-globular-types.md) `G` and
`H`, and consider a
[dependent reflexive globular type](structured-types.dependent-reflexive-globular-types.md)
`K` over `H`. The
{{#concept "base change" Disambiguation="dependent reflexive globular types" Agda=base-change-Dependent-Reflexive-Globular-Type}}
`f*K` is the dependent reflexive globular type over `G` given by

```text
  (f*K)₀ x := K₀ (f₀ x)
  (f*K)' e := K' (f₁ e)
```

where the reflexivity structure of `f*K` is defined separately.

## Definitions

### Base change of dependent reflexive globular types

```agda
dependent-globular-type-base-change-Dependent-Reflexive-Globular-Type :
  {l1 l2 l3 l4 l5 l6 : Level}
  {G : Reflexive-Globular-Type l1 l2} {H : Reflexive-Globular-Type l3 l4}
  (f : reflexive-globular-map G H) →
  Dependent-Reflexive-Globular-Type l5 l6 H →
  Dependent-Globular-Type l5 l6 (globular-type-Reflexive-Globular-Type G)
dependent-globular-type-base-change-Dependent-Reflexive-Globular-Type f K =
  base-change-Dependent-Globular-Type
    ( globular-map-reflexive-globular-map f)
    ( dependent-globular-type-Dependent-Reflexive-Globular-Type K)

0-cell-base-change-Dependent-Reflexive-Globular-Type :
  {l1 l2 l3 l4 l5 l6 : Level}
  {G : Reflexive-Globular-Type l1 l2} {H : Reflexive-Globular-Type l3 l4}
  (f : reflexive-globular-map G H) →
  Dependent-Reflexive-Globular-Type l5 l6 H →
  0-cell-Reflexive-Globular-Type G → UU l5
0-cell-base-change-Dependent-Reflexive-Globular-Type f K =
  0-cell-Dependent-Globular-Type
    ( dependent-globular-type-base-change-Dependent-Reflexive-Globular-Type f K)

1-cell-dependent-globular-type-base-change-Dependent-Reflexive-Globular-Type :
  {l1 l2 l3 l4 l5 l6 : Level}
  {G : Reflexive-Globular-Type l1 l2} {H : Reflexive-Globular-Type l3 l4}
  (f : reflexive-globular-map G H) →
  (K : Dependent-Reflexive-Globular-Type l5 l6 H) →
  {x y : 0-cell-Reflexive-Globular-Type G} →
  0-cell-base-change-Dependent-Reflexive-Globular-Type f K x →
  0-cell-base-change-Dependent-Reflexive-Globular-Type f K y →
  Dependent-Globular-Type l6 l6
    ( 1-cell-globular-type-Reflexive-Globular-Type G x y)
1-cell-dependent-globular-type-base-change-Dependent-Reflexive-Globular-Type
  f K =
  1-cell-dependent-globular-type-Dependent-Globular-Type
    ( dependent-globular-type-base-change-Dependent-Reflexive-Globular-Type f K)

is-reflexive-base-change-Dependent-Reflexive-Globular-Type :
  {l1 l2 l3 l4 l5 l6 : Level}
  {G : Reflexive-Globular-Type l1 l2} {H : Reflexive-Globular-Type l3 l4}
  (f : reflexive-globular-map G H) →
  (K : Dependent-Reflexive-Globular-Type l5 l6 H) →
  is-reflexive-Dependent-Globular-Type G
    ( dependent-globular-type-base-change-Dependent-Reflexive-Globular-Type f K)
refl-1-cell-is-reflexive-Dependent-Globular-Type
  ( is-reflexive-base-change-Dependent-Reflexive-Globular-Type f K) y =
  tr
    ( 1-cell-Dependent-Reflexive-Globular-Type K y y)
    ( inv ( preserves-refl-1-cell-reflexive-globular-map f _))
    ( refl-1-cell-Dependent-Reflexive-Globular-Type K y)
is-reflexive-1-cell-dependent-globular-type-Dependent-Globular-Type
  ( is-reflexive-base-change-Dependent-Reflexive-Globular-Type f K)
  ( y)
  ( y') =
  is-reflexive-base-change-Dependent-Reflexive-Globular-Type
    ( 1-cell-reflexive-globular-map-reflexive-globular-map f)
    ( 1-cell-dependent-reflexive-globular-type-Dependent-Reflexive-Globular-Type
      K y y')

base-change-Dependent-Reflexive-Globular-Type :
  {l1 l2 l3 l4 l5 l6 : Level}
  {G : Reflexive-Globular-Type l1 l2} {H : Reflexive-Globular-Type l3 l4}
  (f : reflexive-globular-map G H) →
  Dependent-Reflexive-Globular-Type l5 l6 H →
  Dependent-Reflexive-Globular-Type l5 l6 G
dependent-globular-type-Dependent-Reflexive-Globular-Type
  ( base-change-Dependent-Reflexive-Globular-Type f K) =
  dependent-globular-type-base-change-Dependent-Reflexive-Globular-Type f K
refl-Dependent-Reflexive-Globular-Type
  ( base-change-Dependent-Reflexive-Globular-Type f K) =
  is-reflexive-base-change-Dependent-Reflexive-Globular-Type f K
```
