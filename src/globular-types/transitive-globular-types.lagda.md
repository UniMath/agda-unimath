# Transitive globular types

```agda
{-# OPTIONS --guardedness #-}

module globular-types.transitive-globular-types where
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

A {{#concept "transitive globular type" Agda=Transitive-Globular-Type}} is a
[globular type](globular-types.globular-types.md) `A`
[equipped](foundation.structure.md) with a binary operator

```text
  - * - : (𝑛+1)-Cell A y z → (𝑛+1)-Cell A x y → (𝑛+1)-Cell A x z
```

at every level $n$.

**Note.** This is not established terminology and may change.

## Definitions

### Transitivity structure on globular types

```agda
record
  is-transitive-Globular-Type
    {l1 l2 : Level} (G : Globular-Type l1 l2) : UU (l1 ⊔ l2)
  where
  coinductive

  field
    comp-1-cell-is-transitive-Globular-Type :
      is-transitive' (1-cell-Globular-Type G)

  field
    is-transitive-1-cell-globular-type-is-transitive-Globular-Type :
      {x y : 0-cell-Globular-Type G} →
      is-transitive-Globular-Type
        ( 1-cell-globular-type-Globular-Type G x y)

open is-transitive-Globular-Type public

module _
  {l1 l2 : Level} {G : Globular-Type l1 l2}
  (t : is-transitive-Globular-Type G)
  where

  comp-2-cell-is-transitive-Globular-Type :
    {x y : 0-cell-Globular-Type G} →
    is-transitive' (2-cell-Globular-Type G {x} {y})
  comp-2-cell-is-transitive-Globular-Type =
    comp-1-cell-is-transitive-Globular-Type
      ( is-transitive-1-cell-globular-type-is-transitive-Globular-Type t)

  is-transitive-2-cell-globular-type-is-transitive-Globular-Type :
    {x y : 0-cell-Globular-Type G}
    {f g : 1-cell-Globular-Type G x y} →
    is-transitive-Globular-Type
      ( 2-cell-globular-type-Globular-Type G f g)
  is-transitive-2-cell-globular-type-is-transitive-Globular-Type =
    is-transitive-1-cell-globular-type-is-transitive-Globular-Type
      ( is-transitive-1-cell-globular-type-is-transitive-Globular-Type t)

module _
  {l1 l2 : Level} {G : Globular-Type l1 l2}
  (t : is-transitive-Globular-Type G)
  where

  comp-3-cell-is-transitive-Globular-Type :
    {x y : 0-cell-Globular-Type G}
    {f g : 1-cell-Globular-Type G x y} →
    is-transitive' (3-cell-Globular-Type G {x} {y} {f} {g})
  comp-3-cell-is-transitive-Globular-Type =
    comp-2-cell-is-transitive-Globular-Type
      ( is-transitive-1-cell-globular-type-is-transitive-Globular-Type t)

  is-transitive-3-cell-globular-type-is-transitive-Globular-Type :
    {x y : 0-cell-Globular-Type G}
    {f g : 1-cell-Globular-Type G x y}
    {s t : 2-cell-Globular-Type G f g} →
    is-transitive-Globular-Type
      ( 3-cell-globular-type-Globular-Type G s t)
  is-transitive-3-cell-globular-type-is-transitive-Globular-Type =
    is-transitive-2-cell-globular-type-is-transitive-Globular-Type
      ( is-transitive-1-cell-globular-type-is-transitive-Globular-Type t)
```

### Transitive globular types

```agda
record
  Transitive-Globular-Type
    (l1 l2 : Level) : UU (lsuc l1 ⊔ lsuc l2)
  where

  constructor
    make-Transitive-Globular-Type
```

The underlying globular type of a transitive globular type:

```agda
  field
    globular-type-Transitive-Globular-Type : Globular-Type l1 l2

  0-cell-Transitive-Globular-Type : UU l1
  0-cell-Transitive-Globular-Type =
    0-cell-Globular-Type globular-type-Transitive-Globular-Type

  1-cell-globular-type-Transitive-Globular-Type :
    (x y : 0-cell-Transitive-Globular-Type) → Globular-Type l2 l2
  1-cell-globular-type-Transitive-Globular-Type =
    1-cell-globular-type-Globular-Type globular-type-Transitive-Globular-Type

  1-cell-Transitive-Globular-Type :
    0-cell-Transitive-Globular-Type → 0-cell-Transitive-Globular-Type → UU l2
  1-cell-Transitive-Globular-Type =
    1-cell-Globular-Type globular-type-Transitive-Globular-Type

  2-cell-globular-type-Transitive-Globular-Type :
    {x y : 0-cell-Transitive-Globular-Type}
    (f g : 1-cell-Transitive-Globular-Type x y) → Globular-Type l2 l2
  2-cell-globular-type-Transitive-Globular-Type =
    2-cell-globular-type-Globular-Type globular-type-Transitive-Globular-Type

  2-cell-Transitive-Globular-Type :
    {x y : 0-cell-Transitive-Globular-Type}
    (f g : 1-cell-Transitive-Globular-Type x y) → UU l2
  2-cell-Transitive-Globular-Type =
    2-cell-Globular-Type globular-type-Transitive-Globular-Type

  3-cell-globular-type-Transitive-Globular-Type :
    {x y : 0-cell-Transitive-Globular-Type}
    {f g : 1-cell-Transitive-Globular-Type x y}
    (s t : 2-cell-Transitive-Globular-Type f g) → Globular-Type l2 l2
  3-cell-globular-type-Transitive-Globular-Type =
    3-cell-globular-type-Globular-Type globular-type-Transitive-Globular-Type

  3-cell-Transitive-Globular-Type :
    {x y : 0-cell-Transitive-Globular-Type}
    {f g : 1-cell-Transitive-Globular-Type x y}
    (s t : 2-cell-Transitive-Globular-Type f g) → UU l2
  3-cell-Transitive-Globular-Type =
    3-cell-Globular-Type globular-type-Transitive-Globular-Type

  globular-structure-Transitive-Globular-Type :
    globular-structure l2 0-cell-Transitive-Globular-Type
  globular-structure-Transitive-Globular-Type =
    globular-structure-0-cell-Globular-Type
      ( globular-type-Transitive-Globular-Type)
```

The composition structure of a transitive globular type:

```agda
  field
    is-transitive-Transitive-Globular-Type :
      is-transitive-Globular-Type globular-type-Transitive-Globular-Type

  comp-1-cell-Transitive-Globular-Type :
    is-transitive' 1-cell-Transitive-Globular-Type
  comp-1-cell-Transitive-Globular-Type =
    comp-1-cell-is-transitive-Globular-Type
      is-transitive-Transitive-Globular-Type

  comp-2-cell-Transitive-Globular-Type :
    {x y : 0-cell-Transitive-Globular-Type} →
    is-transitive' (2-cell-Transitive-Globular-Type {x} {y})
  comp-2-cell-Transitive-Globular-Type =
    comp-2-cell-is-transitive-Globular-Type
      is-transitive-Transitive-Globular-Type

  comp-3-cell-Transitive-Globular-Type :
    {x y : 0-cell-Transitive-Globular-Type}
    {f g : 1-cell-Transitive-Globular-Type x y} →
    is-transitive' (3-cell-Transitive-Globular-Type {x} {y} {f} {g})
  comp-3-cell-Transitive-Globular-Type =
    comp-3-cell-is-transitive-Globular-Type
      is-transitive-Transitive-Globular-Type

  1-cell-transitive-globular-type-Transitive-Globular-Type :
    (x y : 0-cell-Transitive-Globular-Type) →
    Transitive-Globular-Type l2 l2
  globular-type-Transitive-Globular-Type
    ( 1-cell-transitive-globular-type-Transitive-Globular-Type x y) =
    1-cell-globular-type-Transitive-Globular-Type x y
  is-transitive-Transitive-Globular-Type
    ( 1-cell-transitive-globular-type-Transitive-Globular-Type x y) =
    is-transitive-1-cell-globular-type-is-transitive-Globular-Type
      is-transitive-Transitive-Globular-Type

  2-cell-transitive-globular-type-Transitive-Globular-Type :
    {x y : 0-cell-Transitive-Globular-Type} →
    (f g : 1-cell-Transitive-Globular-Type x y) →
    Transitive-Globular-Type l2 l2
  globular-type-Transitive-Globular-Type
    ( 2-cell-transitive-globular-type-Transitive-Globular-Type f g) =
    2-cell-globular-type-Transitive-Globular-Type f g
  is-transitive-Transitive-Globular-Type
    ( 2-cell-transitive-globular-type-Transitive-Globular-Type f g) =
    is-transitive-2-cell-globular-type-is-transitive-Globular-Type
      is-transitive-Transitive-Globular-Type

open Transitive-Globular-Type public
```

### The predicate of being a transitive globular structure

```agda
is-transitive-globular-structure :
  {l1 l2 : Level} {A : UU l1} (G : globular-structure l2 A) → UU (l1 ⊔ l2)
is-transitive-globular-structure G =
  is-transitive-Globular-Type (make-Globular-Type G)

module _
  {l1 l2 : Level} {A : UU l1} {G : globular-structure l2 A}
  (t : is-transitive-globular-structure G)
  where

  comp-1-cell-is-transitive-globular-structure :
    is-transitive' (1-cell-globular-structure G)
  comp-1-cell-is-transitive-globular-structure =
    comp-1-cell-is-transitive-Globular-Type t

  is-transitive-globular-structure-1-cell-is-transitive-globular-structure :
    {x y : A} →
    is-transitive-globular-structure
      ( globular-structure-1-cell-globular-structure G x y)
  is-transitive-globular-structure-1-cell-is-transitive-globular-structure =
    is-transitive-1-cell-globular-type-is-transitive-Globular-Type t

  comp-2-cell-is-transitive-globular-structure :
    {x y : A} → is-transitive' (2-cell-globular-structure G {x} {y})
  comp-2-cell-is-transitive-globular-structure {x} {y} =
    comp-2-cell-is-transitive-Globular-Type t

  is-transitive-globular-structure-2-cell-is-transitive-globular-structure :
    {x y : A} {f g : 1-cell-globular-structure G x y} →
    is-transitive-globular-structure
      ( globular-structure-2-cell-globular-structure G f g)
  is-transitive-globular-structure-2-cell-is-transitive-globular-structure =
    is-transitive-2-cell-globular-type-is-transitive-Globular-Type t

  comp-3-cell-is-transitive-globular-structure :
    {x y : A} {f g : 1-cell-globular-structure G x y} →
    is-transitive' (3-cell-globular-structure G {x} {y} {f} {g})
  comp-3-cell-is-transitive-globular-structure =
    comp-3-cell-is-transitive-Globular-Type t
```

### The type of transitive globular structures on a type

```agda
transitive-globular-structure :
  {l1 : Level} (l2 : Level) (A : UU l1) → UU (l1 ⊔ lsuc l2)
transitive-globular-structure l2 A =
  Σ (globular-structure l2 A) (is-transitive-globular-structure)
```

### Globular maps between transitive globular types

Since there are at least two notions of morphism between transitive globular
types, both of which have an underlying globular map, we record here the
definition of globular maps between transitive globular types.

```agda
module _
  {l1 l2 l3 l4 : Level}
  (G : Transitive-Globular-Type l1 l2) (H : Transitive-Globular-Type l3 l4)
  where

  globular-map-Transitive-Globular-Type : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  globular-map-Transitive-Globular-Type =
    globular-map
      ( globular-type-Transitive-Globular-Type G)
      ( globular-type-Transitive-Globular-Type H)

module _
  {l1 l2 l3 l4 : Level}
  (G : Transitive-Globular-Type l1 l2) (H : Transitive-Globular-Type l3 l4)
  (f : globular-map-Transitive-Globular-Type G H)
  where

  0-cell-globular-map-Transitive-Globular-Type :
    0-cell-Transitive-Globular-Type G → 0-cell-Transitive-Globular-Type H
  0-cell-globular-map-Transitive-Globular-Type =
    0-cell-globular-map f

  1-cell-globular-map-globular-map-Transitive-Globular-Type :
    {x y : 0-cell-Transitive-Globular-Type G} →
    globular-map-Transitive-Globular-Type
      ( 1-cell-transitive-globular-type-Transitive-Globular-Type G x y)
      ( 1-cell-transitive-globular-type-Transitive-Globular-Type H _ _)
  1-cell-globular-map-globular-map-Transitive-Globular-Type =
    1-cell-globular-map-globular-map f

  1-cell-globular-map-Transitive-Globular-Type :
    {x y : 0-cell-Transitive-Globular-Type G} →
    1-cell-Transitive-Globular-Type G x y →
    1-cell-Transitive-Globular-Type H
      ( 0-cell-globular-map-Transitive-Globular-Type x)
      ( 0-cell-globular-map-Transitive-Globular-Type y)
  1-cell-globular-map-Transitive-Globular-Type =
    1-cell-globular-map f
```

## See also

- [Composition structure on globular types](globular-types.composition-structure-globular-types.md)
- [Noncoherent ω-precategories](wild-category-theory.noncoherent-omega-precategories.md)
  are globular types that are both
  [reflexive](globular-types.reflexive-globular-types.md) and transitive.
