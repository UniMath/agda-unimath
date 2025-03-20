# Binary dependent reflexive globular types

```agda
{-# OPTIONS --guardedness #-}

open import foundation.function-extensionality-axiom

module
  globular-types.binary-dependent-reflexive-globular-types
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import globular-types.binary-dependent-globular-types funext
open import globular-types.globular-types
open import globular-types.points-reflexive-globular-types funext
open import globular-types.reflexive-globular-types funext
```

</details>

## Idea

Consider two
[reflexive globular types](globular-types.reflexive-globular-types.md) `G` and
`H`. A
{{#concept "binary dependent reflexive globular type" Agda=Binary-Dependent-Reflexive-Globular-Type}}
`K` over `G` and `H` consists of a
[binary dependent globular type](globular-types.binary-dependent-globular-types.md)
`K` over `G` and `H` equipped with reflexivity structure `refl K`.

A binary dependent globular type `K` over reflexive globular types `G` and `H`
is said to be
{{#concept "reflexive" Disambiguation="binary dependent globular type" Agda=is-reflexive-Binary-Dependent-Globular-Type}}
if it comes equipped with

```text
  refl K : {x : G₀} {y : H₀} (u : K₀ x y) → K₁ (refl G x) (refl G y) u u,
```

such that the binary dependent globular type `K' s t u v` over `G' x x'` and
`H' y y'` comes equipped with reflexivity structure for every `s : G₁ x x'` and
`t : H₁ y y'`.

## Definitions

### The predicate of being a reflexive binary dependent globular type

```agda
record
  is-reflexive-Binary-Dependent-Globular-Type
    {l1 l2 l3 l4 l5 l6 : Level}
    (G : Reflexive-Globular-Type l1 l2)
    (H : Reflexive-Globular-Type l3 l4)
    (K :
      Binary-Dependent-Globular-Type l5 l6
        ( globular-type-Reflexive-Globular-Type G)
        ( globular-type-Reflexive-Globular-Type H)) :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6)
  where
  coinductive

  field
    refl-1-cell-is-reflexive-Binary-Dependent-Globular-Type :
      {x : 0-cell-Reflexive-Globular-Type G}
      {y : 0-cell-Reflexive-Globular-Type H} →
      (u : 0-cell-Binary-Dependent-Globular-Type K x y) →
      1-cell-Binary-Dependent-Globular-Type K u u
        ( refl-1-cell-Reflexive-Globular-Type G)
        ( refl-1-cell-Reflexive-Globular-Type H)

  field
    refl-1-cell-binary-dependent-reflexive-globular-type-is-reflexive-Binary-Dependent-Globular-Type :
      {x x' : 0-cell-Reflexive-Globular-Type G}
      {y y' : 0-cell-Reflexive-Globular-Type H}
      (u : 0-cell-Binary-Dependent-Globular-Type K x y)
      (u' : 0-cell-Binary-Dependent-Globular-Type K x' y') →
      is-reflexive-Binary-Dependent-Globular-Type
        ( 1-cell-reflexive-globular-type-Reflexive-Globular-Type G x x')
        ( 1-cell-reflexive-globular-type-Reflexive-Globular-Type H y y')
        ( 1-cell-binary-dependent-globular-type-Binary-Dependent-Globular-Type
          K u u')

open is-reflexive-Binary-Dependent-Globular-Type public
```

### Binary dependent reflexive globular types

```agda
record
  Binary-Dependent-Reflexive-Globular-Type
    {l1 l2 l3 l4 : Level} (l5 l6 : Level)
    (G : Reflexive-Globular-Type l1 l2)
    (H : Reflexive-Globular-Type l3 l4) :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ lsuc l5 ⊔ lsuc l6)
  where

  field
    binary-dependent-globular-type-Binary-Dependent-Reflexive-Globular-Type :
      Binary-Dependent-Globular-Type l5 l6
        ( globular-type-Reflexive-Globular-Type G)
        ( globular-type-Reflexive-Globular-Type H)

  0-cell-Binary-Dependent-Reflexive-Globular-Type :
    (x : 0-cell-Reflexive-Globular-Type G)
    (y : 0-cell-Reflexive-Globular-Type H) →
    UU l5
  0-cell-Binary-Dependent-Reflexive-Globular-Type =
    0-cell-Binary-Dependent-Globular-Type
      binary-dependent-globular-type-Binary-Dependent-Reflexive-Globular-Type

  1-cell-Binary-Dependent-Reflexive-Globular-Type :
    {x x' : 0-cell-Reflexive-Globular-Type G}
    {y y' : 0-cell-Reflexive-Globular-Type H} →
    0-cell-Binary-Dependent-Reflexive-Globular-Type x y →
    0-cell-Binary-Dependent-Reflexive-Globular-Type x' y' →
    1-cell-Reflexive-Globular-Type G x x' →
    1-cell-Reflexive-Globular-Type H y y' → UU l6
  1-cell-Binary-Dependent-Reflexive-Globular-Type =
    1-cell-Binary-Dependent-Globular-Type
      binary-dependent-globular-type-Binary-Dependent-Reflexive-Globular-Type

  1-cell-binary-dependent-globular-type-Binary-Dependent-Reflexive-Globular-Type :
    {x x' : 0-cell-Reflexive-Globular-Type G}
    {y y' : 0-cell-Reflexive-Globular-Type H} →
    0-cell-Binary-Dependent-Reflexive-Globular-Type x y →
    0-cell-Binary-Dependent-Reflexive-Globular-Type x' y' →
    Binary-Dependent-Globular-Type l6 l6
      ( 1-cell-globular-type-Reflexive-Globular-Type G x x')
      ( 1-cell-globular-type-Reflexive-Globular-Type H y y')
  1-cell-binary-dependent-globular-type-Binary-Dependent-Reflexive-Globular-Type =
    1-cell-binary-dependent-globular-type-Binary-Dependent-Globular-Type
      binary-dependent-globular-type-Binary-Dependent-Reflexive-Globular-Type

  field
    refl-Binary-Dependent-Reflexive-Globular-Type :
      is-reflexive-Binary-Dependent-Globular-Type G H
        binary-dependent-globular-type-Binary-Dependent-Reflexive-Globular-Type

  refl-1-cell-Binary-Dependent-Reflexive-Globular-Type :
    {x : 0-cell-Reflexive-Globular-Type G}
    {y : 0-cell-Reflexive-Globular-Type H}
    (s : 0-cell-Binary-Dependent-Reflexive-Globular-Type x y) →
    1-cell-Binary-Dependent-Reflexive-Globular-Type s s
      ( refl-1-cell-Reflexive-Globular-Type G)
      ( refl-1-cell-Reflexive-Globular-Type H)
  refl-1-cell-Binary-Dependent-Reflexive-Globular-Type =
    refl-1-cell-is-reflexive-Binary-Dependent-Globular-Type
      refl-Binary-Dependent-Reflexive-Globular-Type

  refl-1-cell-binary-dependent-reflexive-globular-type-Binary-Dependent-Reflexive-Globular-Type :
    {x x' : 0-cell-Reflexive-Globular-Type G}
    {y y' : 0-cell-Reflexive-Globular-Type H} →
    (s : 0-cell-Binary-Dependent-Reflexive-Globular-Type x y) →
    (t : 0-cell-Binary-Dependent-Reflexive-Globular-Type x' y') →
    is-reflexive-Binary-Dependent-Globular-Type
      ( 1-cell-reflexive-globular-type-Reflexive-Globular-Type G x x')
      ( 1-cell-reflexive-globular-type-Reflexive-Globular-Type H y y')
      ( 1-cell-binary-dependent-globular-type-Binary-Dependent-Reflexive-Globular-Type
        ( s)
        ( t))
  refl-1-cell-binary-dependent-reflexive-globular-type-Binary-Dependent-Reflexive-Globular-Type =
    refl-1-cell-binary-dependent-reflexive-globular-type-is-reflexive-Binary-Dependent-Globular-Type
      refl-Binary-Dependent-Reflexive-Globular-Type

  1-cell-binary-dependent-reflexive-globular-type-Binary-Dependent-Reflexive-Globular-Type :
    {x x' : 0-cell-Reflexive-Globular-Type G}
    {y y' : 0-cell-Reflexive-Globular-Type H} →
    (s : 0-cell-Binary-Dependent-Reflexive-Globular-Type x y) →
    (t : 0-cell-Binary-Dependent-Reflexive-Globular-Type x' y') →
    Binary-Dependent-Reflexive-Globular-Type l6 l6
      ( 1-cell-reflexive-globular-type-Reflexive-Globular-Type G x x')
      ( 1-cell-reflexive-globular-type-Reflexive-Globular-Type H y y')
  binary-dependent-globular-type-Binary-Dependent-Reflexive-Globular-Type
    ( 1-cell-binary-dependent-reflexive-globular-type-Binary-Dependent-Reflexive-Globular-Type
      ( s)
      ( t)) =
    1-cell-binary-dependent-globular-type-Binary-Dependent-Reflexive-Globular-Type
      ( s)
      ( t)
  refl-Binary-Dependent-Reflexive-Globular-Type
    ( 1-cell-binary-dependent-reflexive-globular-type-Binary-Dependent-Reflexive-Globular-Type
      ( s)
      ( t)) =
    refl-1-cell-binary-dependent-reflexive-globular-type-Binary-Dependent-Reflexive-Globular-Type
      ( s)
      ( t)

open Binary-Dependent-Reflexive-Globular-Type public
```

### Evaluating binary dependent reflexive globular types at points

```agda
globular-type-ev-point-Binary-Dependent-Reflexive-Globular-Type :
  {l1 l2 l3 l4 l5 l6 : Level}
  (G : Reflexive-Globular-Type l1 l2)
  (H : Reflexive-Globular-Type l3 l4)
  (K : Binary-Dependent-Reflexive-Globular-Type l5 l6 G H)
  (x : point-Reflexive-Globular-Type G)
  (y : point-Reflexive-Globular-Type H) →
  Globular-Type l5 l6
globular-type-ev-point-Binary-Dependent-Reflexive-Globular-Type G H K x y =
  ev-point-Binary-Dependent-Globular-Type
    ( binary-dependent-globular-type-Binary-Dependent-Reflexive-Globular-Type K)
    ( point-globular-type-point-Reflexive-Globular-Type G x)
    ( point-globular-type-point-Reflexive-Globular-Type H y)

refl-ev-point-Binary-Dependent-Reflexive-Globular-Type :
  {l1 l2 l3 l4 l5 l6 : Level}
  (G : Reflexive-Globular-Type l1 l2)
  (H : Reflexive-Globular-Type l3 l4)
  (K : Binary-Dependent-Reflexive-Globular-Type l5 l6 G H)
  (x : point-Reflexive-Globular-Type G)
  (y : point-Reflexive-Globular-Type H) →
  is-reflexive-Globular-Type
    ( globular-type-ev-point-Binary-Dependent-Reflexive-Globular-Type G H K x y)
is-reflexive-1-cell-is-reflexive-Globular-Type
  ( refl-ev-point-Binary-Dependent-Reflexive-Globular-Type G H K x y) =
  refl-1-cell-Binary-Dependent-Reflexive-Globular-Type K
is-reflexive-1-cell-globular-type-is-reflexive-Globular-Type
  ( refl-ev-point-Binary-Dependent-Reflexive-Globular-Type G H K x y) =
  refl-ev-point-Binary-Dependent-Reflexive-Globular-Type
    ( 1-cell-reflexive-globular-type-Reflexive-Globular-Type G _ _)
    ( 1-cell-reflexive-globular-type-Reflexive-Globular-Type H _ _)
    ( 1-cell-binary-dependent-reflexive-globular-type-Binary-Dependent-Reflexive-Globular-Type
      ( K)
      ( _)
      ( _))
    ( refl-1-cell-Reflexive-Globular-Type G)
    ( refl-1-cell-Reflexive-Globular-Type H)

ev-point-Binary-Dependent-Reflexive-Globular-Type :
  {l1 l2 l3 l4 l5 l6 : Level}
  (G : Reflexive-Globular-Type l1 l2)
  (H : Reflexive-Globular-Type l3 l4)
  (K : Binary-Dependent-Reflexive-Globular-Type l5 l6 G H)
  (x : point-Reflexive-Globular-Type G)
  (y : point-Reflexive-Globular-Type H) →
  Reflexive-Globular-Type l5 l6
globular-type-Reflexive-Globular-Type
  ( ev-point-Binary-Dependent-Reflexive-Globular-Type G H K x y) =
  globular-type-ev-point-Binary-Dependent-Reflexive-Globular-Type _ _ K x y
refl-Reflexive-Globular-Type
  ( ev-point-Binary-Dependent-Reflexive-Globular-Type G H K x y) =
  refl-ev-point-Binary-Dependent-Reflexive-Globular-Type _ _ K x y
```
