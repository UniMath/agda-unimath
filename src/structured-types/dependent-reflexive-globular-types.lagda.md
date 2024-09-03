# Dependent reflexive globular types

```agda
{-# OPTIONS --guardedness #-}

module structured-types.dependent-reflexive-globular-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import structured-types.dependent-globular-types
open import structured-types.globular-types
open import structured-types.reflexive-globular-types
```

</details>

## Idea

Consider a
[reflexive globular type](structured-types.reflexive-globular-types.md) `G`
equipped with a reflexivity element `ρ`. A
{{#concept "dependent reflexive globular type" Agda=Dependent-Reflexive-Globular-Type}}
over `G` consists of a
[dependent globular type](structured-types.dependent-globular-types.md) `H` over
`G` equipped with a reflexivity element `ρ'` consisting of

```text
ρ'₀ : (x : G₀) (y : H₀ x) → H₁ y y (ρ₀ x)
ρ'₁ : {x x' : G₀} (y : H₀ x) (y' : H₀ x') → is-reflexive (H₁ y y')
```

## Definitions

### The predicate of being a reflexive dependent globular type

```agda
record
  is-reflexive-Dependent-Globular-Type
    { l1 l2 l3 l4 : Level} (G : Reflexive-Globular-Type l1 l2)
    ( H :
      Dependent-Globular-Type l3 l4
        ( globular-type-Reflexive-Globular-Type G)) :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  where
  coinductive
  field
    refl-0-cell-is-reflexive-Dependent-Globular-Type :
      {x : 0-cell-Reflexive-Globular-Type G}
      (y : 0-cell-Dependent-Globular-Type H x) →
      1-cell-Dependent-Globular-Type H y y
        ( refl-0-cell-Reflexive-Globular-Type G)

    is-reflexive-1-cell-dependent-globular-type-Dependent-Globular-Type :
      {x x' : 0-cell-Reflexive-Globular-Type G}
      (y : 0-cell-Dependent-Globular-Type H x)
      (y' : 0-cell-Dependent-Globular-Type H x') →
      is-reflexive-Dependent-Globular-Type
        ( 1-cell-reflexive-globular-type-Reflexive-Globular-Type G x x')
        ( 1-cell-dependent-globular-type-Dependent-Globular-Type H y y')

open is-reflexive-Dependent-Globular-Type public
```

### Dependent reflexive globular types

```agda
record
  Dependent-Reflexive-Globular-Type
    {l1 l2 : Level} (l3 l4 : Level) (G : Reflexive-Globular-Type l1 l2) :
    UU (l1 ⊔ l2 ⊔ lsuc l3 ⊔ lsuc l4)
  where

  field
    dependent-globular-type-Dependent-Reflexive-Globular-Type :
      Dependent-Globular-Type l3 l4 (globular-type-Reflexive-Globular-Type G)

  0-cell-Dependent-Reflexive-Globular-Type :
    0-cell-Reflexive-Globular-Type G → UU l3
  0-cell-Dependent-Reflexive-Globular-Type =
    0-cell-Dependent-Globular-Type
      ( dependent-globular-type-Dependent-Reflexive-Globular-Type)

  1-cell-Dependent-Reflexive-Globular-Type :
    {x x' : 0-cell-Reflexive-Globular-Type G} →
    0-cell-Dependent-Reflexive-Globular-Type x →
    0-cell-Dependent-Reflexive-Globular-Type x' →
    1-cell-Reflexive-Globular-Type G x x' → UU l4
  1-cell-Dependent-Reflexive-Globular-Type =
    1-cell-Dependent-Globular-Type
      ( dependent-globular-type-Dependent-Reflexive-Globular-Type)

  1-cell-dependent-globular-type-Dependent-Reflexive-Globular-Type :
    {x x' : 0-cell-Reflexive-Globular-Type G}
    (y : 0-cell-Dependent-Reflexive-Globular-Type x)
    (y' : 0-cell-Dependent-Reflexive-Globular-Type x') →
    Dependent-Globular-Type l4 l4
      ( 1-cell-globular-type-Reflexive-Globular-Type G x x')
  1-cell-dependent-globular-type-Dependent-Reflexive-Globular-Type =
    1-cell-dependent-globular-type-Dependent-Globular-Type
      ( dependent-globular-type-Dependent-Reflexive-Globular-Type)

  field
    refl-Dependent-Reflexive-Globular-Type :
      is-reflexive-Dependent-Globular-Type G
        ( dependent-globular-type-Dependent-Reflexive-Globular-Type)

  refl-0-cell-Dependent-Reflexive-Globular-Type :
    {x : 0-cell-Reflexive-Globular-Type G}
    (y : 0-cell-Dependent-Reflexive-Globular-Type x) →
    1-cell-Dependent-Reflexive-Globular-Type y y
      ( refl-0-cell-Reflexive-Globular-Type G)
  refl-0-cell-Dependent-Reflexive-Globular-Type =
    refl-0-cell-is-reflexive-Dependent-Globular-Type
      ( refl-Dependent-Reflexive-Globular-Type)

  is-reflexive-1-cell-dependent-globular-type-Dependent-Reflexive-Globular-Type :
    {x x' : 0-cell-Reflexive-Globular-Type G}
    (y : 0-cell-Dependent-Reflexive-Globular-Type x)
    (y' : 0-cell-Dependent-Reflexive-Globular-Type x') →
    is-reflexive-Dependent-Globular-Type
      ( 1-cell-reflexive-globular-type-Reflexive-Globular-Type G x x')
      ( 1-cell-dependent-globular-type-Dependent-Reflexive-Globular-Type y y')
  is-reflexive-1-cell-dependent-globular-type-Dependent-Reflexive-Globular-Type =
    is-reflexive-1-cell-dependent-globular-type-Dependent-Globular-Type
      ( refl-Dependent-Reflexive-Globular-Type)

  1-cell-dependent-reflexive-globular-type-Dependent-Reflexive-Globular-Type :
    {x x' : 0-cell-Reflexive-Globular-Type G}
    (y : 0-cell-Dependent-Reflexive-Globular-Type x)
    (y' : 0-cell-Dependent-Reflexive-Globular-Type x') →
    Dependent-Reflexive-Globular-Type l4 l4
      ( 1-cell-reflexive-globular-type-Reflexive-Globular-Type G x x')
  dependent-globular-type-Dependent-Reflexive-Globular-Type
    ( 1-cell-dependent-reflexive-globular-type-Dependent-Reflexive-Globular-Type
      y y') =
    1-cell-dependent-globular-type-Dependent-Reflexive-Globular-Type y y'
  refl-Dependent-Reflexive-Globular-Type
    ( 1-cell-dependent-reflexive-globular-type-Dependent-Reflexive-Globular-Type
      y y') =
    is-reflexive-1-cell-dependent-globular-type-Dependent-Reflexive-Globular-Type
      y y'

open Dependent-Reflexive-Globular-Type public
```

### The family of reflexive globular types obtained from a dependent reflexive globular type

Given a dependent reflexive globular type `H` over `G` we construct a family of
reflexive globular types indexed by the type of `0`-cells of `G`. This
construction makes essential use of the reflexivity elements of the base
reflexive globular type.

```agda
globular-structure-family-globular-types-Dependent-Reflexive-Globular-Type :
  {l1 l2 l3 l4 : Level} {G : Reflexive-Globular-Type l1 l2}
  (H : Dependent-Reflexive-Globular-Type l3 l4 G)
  (x : 0-cell-Reflexive-Globular-Type G) →
  globular-structure l4 (0-cell-Dependent-Reflexive-Globular-Type H x)
1-cell-globular-structure
  ( globular-structure-family-globular-types-Dependent-Reflexive-Globular-Type
    { G = G}
    ( H)
    ( x))
  ( u)
  ( v) =
    1-cell-Dependent-Reflexive-Globular-Type H u v
      ( refl-0-cell-Reflexive-Globular-Type G)
globular-structure-1-cell-globular-structure
  ( globular-structure-family-globular-types-Dependent-Reflexive-Globular-Type
    { G = G}
    ( H)
    ( x))
  ( u)
  ( v) =
  globular-structure-family-globular-types-Dependent-Reflexive-Globular-Type
    ( 1-cell-dependent-reflexive-globular-type-Dependent-Reflexive-Globular-Type
      H u v)
    ( refl-0-cell-Reflexive-Globular-Type G)

family-globular-types-Dependent-Reflexive-Globular-Type :
  {l1 l2 l3 l4 : Level} {G : Reflexive-Globular-Type l1 l2}
  (H : Dependent-Reflexive-Globular-Type l3 l4 G) →
  0-cell-Reflexive-Globular-Type G → Globular-Type l3 l4
pr1 (family-globular-types-Dependent-Reflexive-Globular-Type H x) =
  0-cell-Dependent-Reflexive-Globular-Type H x
pr2 (family-globular-types-Dependent-Reflexive-Globular-Type H x) =
  globular-structure-family-globular-types-Dependent-Reflexive-Globular-Type
    ( H)
    ( x)

is-reflexive-family-globular-types-Dependent-Reflexive-Globular-Type :
  {l1 l2 l3 l4 : Level} {G : Reflexive-Globular-Type l1 l2}
  (H : Dependent-Reflexive-Globular-Type l3 l4 G)
  (x : 0-cell-Reflexive-Globular-Type G) →
  is-reflexive-Globular-Type
    ( family-globular-types-Dependent-Reflexive-Globular-Type H x)
is-reflexive-1-cell-is-reflexive-globular-structure
  ( is-reflexive-family-globular-types-Dependent-Reflexive-Globular-Type H x) =
  refl-0-cell-Dependent-Reflexive-Globular-Type H
is-reflexive-globular-structure-1-cell-is-reflexive-globular-structure
  ( is-reflexive-family-globular-types-Dependent-Reflexive-Globular-Type
    { G = G} H x)
  ( u)
  ( v) =
  is-reflexive-family-globular-types-Dependent-Reflexive-Globular-Type
    ( 1-cell-dependent-reflexive-globular-type-Dependent-Reflexive-Globular-Type
      H u v)
    ( refl-0-cell-Reflexive-Globular-Type G)

module _
  {l1 l2 l3 l4 : Level} {G : Reflexive-Globular-Type l1 l2}
  (H : Dependent-Reflexive-Globular-Type l3 l4 G)
  where

  family-reflexive-globular-types-Dependent-Reflexive-Globular-Type :
    0-cell-Reflexive-Globular-Type G → Reflexive-Globular-Type l3 l4
  globular-type-Reflexive-Globular-Type
    ( family-reflexive-globular-types-Dependent-Reflexive-Globular-Type x) =
    family-globular-types-Dependent-Reflexive-Globular-Type H x
  refl-Reflexive-Globular-Type
    ( family-reflexive-globular-types-Dependent-Reflexive-Globular-Type x) =
    is-reflexive-family-globular-types-Dependent-Reflexive-Globular-Type H x
```
