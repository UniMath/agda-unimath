# Base change of dependent globular types

```agda
{-# OPTIONS --guardedness #-}
open import foundation.function-extensionality-axiom

module globular-types.base-change-dependent-globular-types
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import globular-types.dependent-globular-types funext
open import globular-types.globular-maps funext
open import globular-types.globular-types
```

</details>

## Idea

Consider a [dependent globular type](globular-types.dependent-globular-types.md)
`H` over `G`, and consider a [globular map](globular-types.globular-maps.md)
`f : K → G`. The
{{#concept "base change" Disambiguation="dependent globular types" agda=base-change-Dependent-Globular-Type}}
of `H` along `f` is the dependent globular type `f*H` given by

```text
  (f*H)₀ x := H₀ (f₀ x)
  (f*H)₁ y y' := H₁.
```

## Definitions

```agda
base-change-Dependent-Globular-Type :
  {l1 l2 l3 l4 l5 l6 : Level}
  {G : Globular-Type l1 l2} {K : Globular-Type l3 l4}
  (f : globular-map K G) →
  Dependent-Globular-Type l5 l6 G → Dependent-Globular-Type l5 l6 K
0-cell-Dependent-Globular-Type
  ( base-change-Dependent-Globular-Type f H)
  ( x) =
  0-cell-Dependent-Globular-Type H (0-cell-globular-map f x)
1-cell-dependent-globular-type-Dependent-Globular-Type
  ( base-change-Dependent-Globular-Type f H) y y' =
  base-change-Dependent-Globular-Type
    ( 1-cell-globular-map-globular-map f)
    ( 1-cell-dependent-globular-type-Dependent-Globular-Type H y y')

module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {G : Globular-Type l1 l2} {K : Globular-Type l3 l4}
  (f : globular-map K G) (H : Dependent-Globular-Type l5 l6 G)
  where

  0-cell-base-change-Dependent-Globular-Type :
    0-cell-Globular-Type K → UU l5
  0-cell-base-change-Dependent-Globular-Type =
    0-cell-Dependent-Globular-Type (base-change-Dependent-Globular-Type f H)

  1-cell-dependent-globular-type-base-change-Dependent-Globular-Type :
    {x x' : 0-cell-Globular-Type K}
    (y : 0-cell-base-change-Dependent-Globular-Type x)
    (y' : 0-cell-base-change-Dependent-Globular-Type x') →
    Dependent-Globular-Type l6 l6
      ( 1-cell-globular-type-Globular-Type K x x')
  1-cell-dependent-globular-type-base-change-Dependent-Globular-Type =
    1-cell-dependent-globular-type-Dependent-Globular-Type
      ( base-change-Dependent-Globular-Type f H)

  1-cell-base-change-Dependent-Globular-Type :
    {x x' : 0-cell-Globular-Type K}
    (y : 0-cell-base-change-Dependent-Globular-Type x)
    (y' : 0-cell-base-change-Dependent-Globular-Type x') →
    1-cell-Globular-Type K x x' → UU l6
  1-cell-base-change-Dependent-Globular-Type =
    1-cell-Dependent-Globular-Type (base-change-Dependent-Globular-Type f H)
```
