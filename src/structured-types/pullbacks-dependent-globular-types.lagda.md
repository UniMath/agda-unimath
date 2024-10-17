# Pullbacks of dependent globular types

```agda
{-# OPTIONS --guardedness #-}

module structured-types.pullbacks-dependent-globular-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import structured-types.dependent-globular-types
open import structured-types.globular-maps
open import structured-types.globular-types
```

</details>

## Idea

Consider a [dependent globular type](structured-types.dependent-globular-types.md) `H` over `G`, and consider a [globular map](structured-types.globular-maps.md) `f : K → G`. The {{#concept "pullback" Disambiguation="dependent globular types" agda=pullback-Dependent-Globular-Type}} of `H` along `f` is the dependent globular type `f*H` given by

```text
  (f*H)₀ x := H₀ (f₀ x)
  (f*H)₁ y y' := H₁
```

## Definitions

```agda
pullback-Dependent-Globular-Type :
  {l1 l2 l3 l4 l5 l6 : Level}
  {G : Globular-Type l1 l2} {K : Globular-Type l3 l4}
  (f : globular-map K G) →
  Dependent-Globular-Type l5 l6 G → Dependent-Globular-Type l5 l6 K
0-cell-Dependent-Globular-Type
  ( pullback-Dependent-Globular-Type f H)
  ( x) =
  0-cell-Dependent-Globular-Type H (0-cell-globular-map f x)
1-cell-dependent-globular-type-Dependent-Globular-Type
  ( pullback-Dependent-Globular-Type f H) y y' =
  pullback-Dependent-Globular-Type
    ( 1-cell-globular-map-globular-map f)
    ( 1-cell-dependent-globular-type-Dependent-Globular-Type H y y')

module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {G : Globular-Type l1 l2} {K : Globular-Type l3 l4}
  (f : globular-map K G) (H : Dependent-Globular-Type l5 l6 G)
  where

  0-cell-pullback-Dependent-Globular-Type :
    0-cell-Globular-Type K → UU l5
  0-cell-pullback-Dependent-Globular-Type =
    0-cell-Dependent-Globular-Type (pullback-Dependent-Globular-Type f H)

  1-cell-dependent-globular-type-pullback-Dependent-Globular-Type :
    {x x' : 0-cell-Globular-Type K}
    (y : 0-cell-pullback-Dependent-Globular-Type x)
    (y' : 0-cell-pullback-Dependent-Globular-Type x') →
    Dependent-Globular-Type l6 l6
      ( 1-cell-globular-type-Globular-Type K x x')
  1-cell-dependent-globular-type-pullback-Dependent-Globular-Type =
    1-cell-dependent-globular-type-Dependent-Globular-Type
      ( pullback-Dependent-Globular-Type f H)

  1-cell-pullback-Dependent-Globular-Type :
    {x x' : 0-cell-Globular-Type K}
    (y : 0-cell-pullback-Dependent-Globular-Type x)
    (y' : 0-cell-pullback-Dependent-Globular-Type x') →
    1-cell-Globular-Type K x x' → UU l6
  1-cell-pullback-Dependent-Globular-Type =
    1-cell-Dependent-Globular-Type (pullback-Dependent-Globular-Type f H)
```
