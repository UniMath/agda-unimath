# Reflexive globular types

```agda
{-# OPTIONS --guardedness #-}

module globular-types.reflexive-globular-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import globular-types.globular-maps
open import globular-types.globular-types
```

</details>

## Idea

A [globular type](globular-types.globular-types.md) is
{{#concept "reflexive" Disambiguation="globular type" Agda=is-reflexive-globular-structure}}
if every $n$-cell `x` comes with a choice of $(n+1)$-cell from `x` to `x`.

## Definitions

### Reflexivity structure on globular types

```agda
record
  is-reflexive-Globular-Type
    {l1 l2 : Level} (G : Globular-Type l1 l2) : UU (l1 ⊔ l2)
  where
  coinductive

  field
    is-reflexive-1-cell-is-reflexive-Globular-Type :
      is-reflexive (1-cell-Globular-Type G)

  field
    is-reflexive-1-cell-globular-type-is-reflexive-Globular-Type :
      {x y : 0-cell-Globular-Type G} →
      is-reflexive-Globular-Type (1-cell-globular-type-Globular-Type G x y)

open is-reflexive-Globular-Type public

module _
  {l1 l2 : Level} {G : Globular-Type l1 l2}
  (r : is-reflexive-Globular-Type G)
  where

  refl-2-cell-is-reflexive-Globular-Type :
    {x : 0-cell-Globular-Type G} →
    1-cell-Globular-Type G x x
  refl-2-cell-is-reflexive-Globular-Type =
    is-reflexive-1-cell-is-reflexive-Globular-Type r _

  is-reflexive-2-cell-is-reflexive-Globular-Type :
    {x y : 0-cell-Globular-Type G} →
    is-reflexive (2-cell-Globular-Type G {x} {y})
  is-reflexive-2-cell-is-reflexive-Globular-Type =
    is-reflexive-1-cell-is-reflexive-Globular-Type
      ( is-reflexive-1-cell-globular-type-is-reflexive-Globular-Type r)

  refl-3-cell-is-reflexive-Globular-Type :
    {x y : 0-cell-Globular-Type G} {f : 1-cell-Globular-Type G x y} →
    2-cell-Globular-Type G f f
  refl-3-cell-is-reflexive-Globular-Type =
    is-reflexive-1-cell-is-reflexive-Globular-Type
      ( is-reflexive-1-cell-globular-type-is-reflexive-Globular-Type r)
      ( _)

  is-reflexive-2-cell-globular-type-is-reflexive-Globular-Type :
    {x y : 0-cell-Globular-Type G} →
    {f g : 1-cell-Globular-Type G x y} →
    is-reflexive-Globular-Type
      ( 2-cell-globular-type-Globular-Type G {x} {y} f g)
  is-reflexive-2-cell-globular-type-is-reflexive-Globular-Type =
    is-reflexive-1-cell-globular-type-is-reflexive-Globular-Type
      ( is-reflexive-1-cell-globular-type-is-reflexive-Globular-Type r)

module _
  {l1 l2 : Level} (G : Globular-Type l1 l2)
  (r : is-reflexive-Globular-Type G)
  where

  is-reflexive-3-cell-is-reflexive-Globular-Type :
    {x y : 0-cell-Globular-Type G} →
    {f g : 1-cell-Globular-Type G x y} →
    is-reflexive (3-cell-Globular-Type G {x} {y} {f} {g})
  is-reflexive-3-cell-is-reflexive-Globular-Type =
    is-reflexive-2-cell-is-reflexive-Globular-Type
      ( is-reflexive-1-cell-globular-type-is-reflexive-Globular-Type r)

  refl-4-cell-is-reflexive-Globular-Type :
    {x y : 0-cell-Globular-Type G} →
    {f g : 1-cell-Globular-Type G x y} →
    {s : 2-cell-Globular-Type G f g} → 3-cell-Globular-Type G s s
  refl-4-cell-is-reflexive-Globular-Type =
    refl-3-cell-is-reflexive-Globular-Type
      ( is-reflexive-1-cell-globular-type-is-reflexive-Globular-Type r)

  is-reflexive-3-cell-globular-type-is-reflexive-Globular-Type :
    {x y : 0-cell-Globular-Type G} →
    {f g : 1-cell-Globular-Type G x y}
    {s t : 2-cell-Globular-Type G f g} →
    is-reflexive-Globular-Type
      ( 3-cell-globular-type-Globular-Type G {x} {y} {f} {g} s t)
  is-reflexive-3-cell-globular-type-is-reflexive-Globular-Type =
    is-reflexive-2-cell-globular-type-is-reflexive-Globular-Type
      ( is-reflexive-1-cell-globular-type-is-reflexive-Globular-Type r)
```

### Reflexive globular types

```agda
record
  Reflexive-Globular-Type (l1 l2 : Level) : UU (lsuc l1 ⊔ lsuc l2)
  where

  eta-equality
```

The underlying globular type of a reflexive globular type:

```agda
  field
    globular-type-Reflexive-Globular-Type : Globular-Type l1 l2

  0-cell-Reflexive-Globular-Type : UU l1
  0-cell-Reflexive-Globular-Type =
    0-cell-Globular-Type globular-type-Reflexive-Globular-Type

  1-cell-Reflexive-Globular-Type :
    0-cell-Reflexive-Globular-Type → 0-cell-Reflexive-Globular-Type → UU l2
  1-cell-Reflexive-Globular-Type =
    1-cell-Globular-Type globular-type-Reflexive-Globular-Type

  2-cell-Reflexive-Globular-Type :
    {x x' : 0-cell-Reflexive-Globular-Type}
    (y y' : 1-cell-Reflexive-Globular-Type x x') → UU l2
  2-cell-Reflexive-Globular-Type =
    2-cell-Globular-Type globular-type-Reflexive-Globular-Type

  3-cell-Reflexive-Globular-Type :
    {x x' : 0-cell-Reflexive-Globular-Type}
    {y y' : 1-cell-Reflexive-Globular-Type x x'} →
    (z z' : 2-cell-Reflexive-Globular-Type y y') → UU l2
  3-cell-Reflexive-Globular-Type =
    3-cell-Globular-Type globular-type-Reflexive-Globular-Type

  globular-structure-Reflexive-Globular-Type :
    globular-structure l2 0-cell-Reflexive-Globular-Type
  globular-structure-Reflexive-Globular-Type =
    globular-structure-0-cell-Globular-Type
      ( globular-type-Reflexive-Globular-Type)
```

The reflexivity structure of a reflexive globular type:

```agda
  field
    refl-Reflexive-Globular-Type :
      is-reflexive-Globular-Type globular-type-Reflexive-Globular-Type

  refl-1-cell-Reflexive-Globular-Type :
    {x : 0-cell-Reflexive-Globular-Type} →
    1-cell-Reflexive-Globular-Type x x
  refl-1-cell-Reflexive-Globular-Type =
    is-reflexive-1-cell-is-reflexive-Globular-Type
      ( refl-Reflexive-Globular-Type)
      ( _)

  1-cell-globular-type-Reflexive-Globular-Type :
    (x y : 0-cell-Reflexive-Globular-Type) → Globular-Type l2 l2
  1-cell-globular-type-Reflexive-Globular-Type =
    1-cell-globular-type-Globular-Type globular-type-Reflexive-Globular-Type

  refl-2-cell-Reflexive-Globular-Type :
    {x y : 0-cell-Reflexive-Globular-Type}
    {f : 1-cell-Reflexive-Globular-Type x y} →
    2-cell-Reflexive-Globular-Type f f
  refl-2-cell-Reflexive-Globular-Type =
    is-reflexive-2-cell-is-reflexive-Globular-Type
      ( refl-Reflexive-Globular-Type)
      ( _)

  refl-2-cell-globular-type-Reflexive-Globular-Type :
    {x y : 0-cell-Reflexive-Globular-Type} →
    is-reflexive-Globular-Type
      ( 1-cell-globular-type-Reflexive-Globular-Type x y)
  refl-2-cell-globular-type-Reflexive-Globular-Type =
    is-reflexive-1-cell-globular-type-is-reflexive-Globular-Type
      refl-Reflexive-Globular-Type
```

The reflexive globular type of 1-cells of a reflexive globular type:

```agda
  1-cell-reflexive-globular-type-Reflexive-Globular-Type :
    (x y : 0-cell-Reflexive-Globular-Type) → Reflexive-Globular-Type l2 l2
  globular-type-Reflexive-Globular-Type
    ( 1-cell-reflexive-globular-type-Reflexive-Globular-Type x y) =
    1-cell-globular-type-Reflexive-Globular-Type x y
  refl-Reflexive-Globular-Type
    ( 1-cell-reflexive-globular-type-Reflexive-Globular-Type x y) =
    refl-2-cell-globular-type-Reflexive-Globular-Type

open Reflexive-Globular-Type public
```

### The predicate of being a reflexive globular structure

```agda
is-reflexive-globular-structure :
  {l1 l2 : Level} {A : UU l1} → globular-structure l2 A → UU (l1 ⊔ l2)
is-reflexive-globular-structure G =
  is-reflexive-Globular-Type (make-Globular-Type G)

module _
  {l1 l2 : Level} {A : UU l1} (G : globular-structure l2 A)
  (r : is-reflexive-globular-structure G)
  where

  is-reflexive-1-cell-is-reflexive-globular-structure :
    is-reflexive (1-cell-globular-structure G)
  is-reflexive-1-cell-is-reflexive-globular-structure =
    is-reflexive-1-cell-is-reflexive-Globular-Type r

  refl-2-cell-is-reflexive-globular-structure :
    {x : A} → 1-cell-globular-structure G x x
  refl-2-cell-is-reflexive-globular-structure =
    is-reflexive-1-cell-is-reflexive-Globular-Type r _

  is-reflexive-globular-structure-1-cell-is-reflexive-globular-structure :
    {x y : A} →
    is-reflexive-globular-structure
      ( globular-structure-1-cell-globular-structure G x y)
  is-reflexive-globular-structure-1-cell-is-reflexive-globular-structure =
    is-reflexive-1-cell-globular-type-is-reflexive-Globular-Type r

  is-reflexive-2-cell-is-reflexive-globular-structure :
    {x y : A} → is-reflexive (2-cell-globular-structure G {x} {y})
  is-reflexive-2-cell-is-reflexive-globular-structure {x} {y} =
    is-reflexive-2-cell-is-reflexive-Globular-Type r

  refl-3-cell-is-reflexive-globular-structure :
    {x y : A} {f : 1-cell-globular-structure G x y} →
    2-cell-globular-structure G f f
  refl-3-cell-is-reflexive-globular-structure =
    is-reflexive-2-cell-is-reflexive-globular-structure _

  is-reflexive-globular-structure-2-cell-is-reflexive-globular-structure :
    {x y : A}
    {f g : 1-cell-globular-structure G x y} →
    is-reflexive-globular-structure
      ( globular-structure-2-cell-globular-structure G f g)
  is-reflexive-globular-structure-2-cell-is-reflexive-globular-structure =
    is-reflexive-2-cell-globular-type-is-reflexive-Globular-Type r

  is-reflexive-3-cell-is-reflexive-globular-structure :
    {x y : A} {f g : 1-cell-globular-structure G x y} →
    is-reflexive (3-cell-globular-structure G {x} {y} {f} {g})
  is-reflexive-3-cell-is-reflexive-globular-structure =
    is-reflexive-3-cell-is-reflexive-Globular-Type (make-Globular-Type G) r

  refl-4-cell-is-reflexive-globular-structure :
    {x y : A}
    {f g : 1-cell-globular-structure G x y}
    {H : 2-cell-globular-structure G f g} →
    3-cell-globular-structure G H H
  refl-4-cell-is-reflexive-globular-structure {x} {y} {f} {g} {H} =
    is-reflexive-3-cell-is-reflexive-globular-structure _
```

### The type of reflexive globular structures

```agda
reflexive-globular-structure :
  {l1 : Level} (l2 : Level) (A : UU l1) → UU (l1 ⊔ lsuc l2)
reflexive-globular-structure l2 A =
  Σ (globular-structure l2 A) (is-reflexive-globular-structure)
```

### Globular maps between reflexive globular types

Since there are at least two notions of morphism between reflexive globular
types, both of which have an underlying globular map, we record here the
definition of globular maps between reflexive globular types.

```agda
module _
  {l1 l2 l3 l4 : Level}
  (G : Reflexive-Globular-Type l1 l2) (H : Reflexive-Globular-Type l3 l4)
  where

  globular-map-Reflexive-Globular-Type : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  globular-map-Reflexive-Globular-Type =
    globular-map
      ( globular-type-Reflexive-Globular-Type G)
      ( globular-type-Reflexive-Globular-Type H)

module _
  {l1 l2 l3 l4 : Level}
  (G : Reflexive-Globular-Type l1 l2) (H : Reflexive-Globular-Type l3 l4)
  (f : globular-map-Reflexive-Globular-Type G H)
  where

  0-cell-globular-map-Reflexive-Globular-Type :
    0-cell-Reflexive-Globular-Type G → 0-cell-Reflexive-Globular-Type H
  0-cell-globular-map-Reflexive-Globular-Type =
    0-cell-globular-map f

  1-cell-globular-map-globular-map-Reflexive-Globular-Type :
    {x y : 0-cell-Reflexive-Globular-Type G} →
    globular-map-Reflexive-Globular-Type
      ( 1-cell-reflexive-globular-type-Reflexive-Globular-Type G x y)
      ( 1-cell-reflexive-globular-type-Reflexive-Globular-Type H _ _)
  1-cell-globular-map-globular-map-Reflexive-Globular-Type =
    1-cell-globular-map-globular-map f
```

## See also

- [Colax reflexive globular maps](globular-types.colax-reflexive-globular-maps.md)
- [Lax reflexive globular maps](globular-types.lax-reflexive-globular-maps.md)
- [Reflexive globular maps](globular-types.reflexive-globular-maps.md)
- [Noncoherent ω-precategories](wild-category-theory.noncoherent-omega-precategories.md)
  are globular types that are both reflexive and
  [transitive](globular-types.transitive-globular-types.md).
