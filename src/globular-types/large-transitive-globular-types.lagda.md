# Large transitive globular types

```agda
{-# OPTIONS --guardedness #-}

module globular-types.large-transitive-globular-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import globular-types.globular-types
open import globular-types.large-globular-maps
open import globular-types.large-globular-types
open import globular-types.transitive-globular-types
```

</details>

## Idea

A
{{#concept "large transitive globular type" Agda=Large-Transitive-Globular-Type}}
is a [large globular type](globular-types.large-globular-types.md) `A`
[equipped](foundation.structure.md) with a binary operator

```text
  - * - : (𝑛+1)-Cell A y z → (𝑛+1)-Cell A x y → (𝑛+1)-Cell A x z
```

at every level $n$.

## Definition

### Transitivity structure on large globular types

```agda
record
  is-transitive-Large-Globular-Type
    {α : Level → Level} {β : Level → Level → Level}
    (G : Large-Globular-Type α β) : UUω
  where

  field
    comp-1-cell-is-transitive-Large-Globular-Type :
      {l1 l2 l3 : Level}
      {x : 0-cell-Large-Globular-Type G l1}
      {y : 0-cell-Large-Globular-Type G l2}
      {z : 0-cell-Large-Globular-Type G l3} →
      1-cell-Large-Globular-Type G y z →
      1-cell-Large-Globular-Type G x y →
      1-cell-Large-Globular-Type G x z

  field
    is-transitive-1-cell-globular-type-is-transitive-Large-Globular-Type :
      {l1 l2 : Level}
      {x : 0-cell-Large-Globular-Type G l1}
      {y : 0-cell-Large-Globular-Type G l2} →
      is-transitive-Globular-Type
        ( 1-cell-globular-type-Large-Globular-Type G x y)

open is-transitive-Large-Globular-Type public

module _
  {α : Level → Level} {β : Level → Level → Level}
  {G : Large-Globular-Type α β}
  (τ : is-transitive-Large-Globular-Type G)
  where

  comp-2-cell-is-transitive-Large-Globular-Type :
    {l1 l2 : Level}
    {x : 0-cell-Large-Globular-Type G l1}
    {y : 0-cell-Large-Globular-Type G l2}
    {f g h : 1-cell-Large-Globular-Type G x y} →
    2-cell-Large-Globular-Type G g h →
    2-cell-Large-Globular-Type G f g →
    2-cell-Large-Globular-Type G f h
  comp-2-cell-is-transitive-Large-Globular-Type =
    comp-1-cell-is-transitive-Globular-Type
      ( is-transitive-1-cell-globular-type-is-transitive-Large-Globular-Type τ)

  is-transitive-2-cell-globular-type-is-transitive-Large-Globular-Type :
    {l1 l2 : Level}
    {x : 0-cell-Large-Globular-Type G l1}
    {y : 0-cell-Large-Globular-Type G l2}
    {f g : 1-cell-Large-Globular-Type G x y} →
    is-transitive-Globular-Type
      ( 2-cell-globular-type-Large-Globular-Type G f g)
  is-transitive-2-cell-globular-type-is-transitive-Large-Globular-Type =
    is-transitive-1-cell-globular-type-is-transitive-Globular-Type
      ( is-transitive-1-cell-globular-type-is-transitive-Large-Globular-Type τ)

  comp-3-cell-is-transitive-Large-Globular-Type :
    {l1 l2 : Level}
    {x : 0-cell-Large-Globular-Type G l1}
    {y : 0-cell-Large-Globular-Type G l2}
    {f g : 1-cell-Large-Globular-Type G x y}
    {s t u : 2-cell-Large-Globular-Type G f g} →
    3-cell-Large-Globular-Type G t u →
    3-cell-Large-Globular-Type G s t →
    3-cell-Large-Globular-Type G s u
  comp-3-cell-is-transitive-Large-Globular-Type =
    comp-2-cell-is-transitive-Globular-Type
      ( is-transitive-1-cell-globular-type-is-transitive-Large-Globular-Type τ)

  is-transitive-3-cell-globular-type-is-transitive-Large-Globular-Type :
    {l1 l2 : Level}
    {x : 0-cell-Large-Globular-Type G l1}
    {y : 0-cell-Large-Globular-Type G l2}
    {f g : 1-cell-Large-Globular-Type G x y}
    {s t : 2-cell-Large-Globular-Type G f g} →
    is-transitive-Globular-Type
      ( 3-cell-globular-type-Large-Globular-Type G s t)
  is-transitive-3-cell-globular-type-is-transitive-Large-Globular-Type =
    is-transitive-2-cell-globular-type-is-transitive-Globular-Type
      ( is-transitive-1-cell-globular-type-is-transitive-Large-Globular-Type τ)
```

### Large transitive globular types

```agda
record
  Large-Transitive-Globular-Type
    (α : Level → Level) (β : Level → Level → Level) : UUω
    where

    field
      large-globular-type-Large-Transitive-Globular-Type :
        Large-Globular-Type α β

    0-cell-Large-Transitive-Globular-Type : (l : Level) → UU (α l)
    0-cell-Large-Transitive-Globular-Type =
      0-cell-Large-Globular-Type
        large-globular-type-Large-Transitive-Globular-Type

    1-cell-Large-Transitive-Globular-Type :
      {l1 l2 : Level}
      (x : 0-cell-Large-Transitive-Globular-Type l1)
      (y : 0-cell-Large-Transitive-Globular-Type l2) → UU (β l1 l2)
    1-cell-Large-Transitive-Globular-Type =
      1-cell-Large-Globular-Type
        large-globular-type-Large-Transitive-Globular-Type

    1-cell-globular-type-Large-Transitive-Globular-Type :
      {l1 l2 : Level}
      (x : 0-cell-Large-Transitive-Globular-Type l1)
      (y : 0-cell-Large-Transitive-Globular-Type l2) →
      Globular-Type (β l1 l2) (β l1 l2)
    1-cell-globular-type-Large-Transitive-Globular-Type =
      1-cell-globular-type-Large-Globular-Type
        large-globular-type-Large-Transitive-Globular-Type

    2-cell-Large-Transitive-Globular-Type :
      {l1 l2 : Level}
      {x : 0-cell-Large-Transitive-Globular-Type l1}
      {y : 0-cell-Large-Transitive-Globular-Type l2}
      (f g : 1-cell-Large-Transitive-Globular-Type x y) → UU (β l1 l2)
    2-cell-Large-Transitive-Globular-Type =
      2-cell-Large-Globular-Type
        large-globular-type-Large-Transitive-Globular-Type

    2-cell-globular-type-Large-Transitive-Globular-Type :
      {l1 l2 : Level}
      {x : 0-cell-Large-Transitive-Globular-Type l1}
      {y : 0-cell-Large-Transitive-Globular-Type l2}
      (f g : 1-cell-Large-Transitive-Globular-Type x y) →
      Globular-Type (β l1 l2) (β l1 l2)
    2-cell-globular-type-Large-Transitive-Globular-Type =
      2-cell-globular-type-Large-Globular-Type
        large-globular-type-Large-Transitive-Globular-Type

    3-cell-Large-Transitive-Globular-Type :
      {l1 l2 : Level}
      {x : 0-cell-Large-Transitive-Globular-Type l1}
      {y : 0-cell-Large-Transitive-Globular-Type l2}
      {f g : 1-cell-Large-Transitive-Globular-Type x y}
      (s t : 2-cell-Large-Transitive-Globular-Type f g) → UU (β l1 l2)
    3-cell-Large-Transitive-Globular-Type =
      3-cell-Large-Globular-Type
        large-globular-type-Large-Transitive-Globular-Type

    3-cell-globular-type-Large-Transitive-Globular-Type :
      {l1 l2 : Level}
      {x : 0-cell-Large-Transitive-Globular-Type l1}
      {y : 0-cell-Large-Transitive-Globular-Type l2}
      {f g : 1-cell-Large-Transitive-Globular-Type x y}
      (s t : 2-cell-Large-Transitive-Globular-Type f g) →
      Globular-Type (β l1 l2) (β l1 l2)
    3-cell-globular-type-Large-Transitive-Globular-Type =
      3-cell-globular-type-Large-Globular-Type
        large-globular-type-Large-Transitive-Globular-Type

    field
      is-transitive-Large-Transitive-Globular-Type :
        is-transitive-Large-Globular-Type
          large-globular-type-Large-Transitive-Globular-Type

    comp-1-cell-Large-Transitive-Globular-Type :
      {l1 l2 l3 : Level}
      {x : 0-cell-Large-Transitive-Globular-Type l1}
      {y : 0-cell-Large-Transitive-Globular-Type l2}
      {z : 0-cell-Large-Transitive-Globular-Type l3} →
      1-cell-Large-Transitive-Globular-Type y z →
      1-cell-Large-Transitive-Globular-Type x y →
      1-cell-Large-Transitive-Globular-Type x z
    comp-1-cell-Large-Transitive-Globular-Type =
      comp-1-cell-is-transitive-Large-Globular-Type
        is-transitive-Large-Transitive-Globular-Type

    1-cell-transitive-globular-type-Large-Transitive-Globular-Type :
      {l1 l2 : Level}
      (x : 0-cell-Large-Transitive-Globular-Type l1)
      (y : 0-cell-Large-Transitive-Globular-Type l2) →
      Transitive-Globular-Type (β l1 l2) (β l1 l2)
    globular-type-Transitive-Globular-Type
      ( 1-cell-transitive-globular-type-Large-Transitive-Globular-Type x y) =
      1-cell-globular-type-Large-Transitive-Globular-Type x y
    is-transitive-Transitive-Globular-Type
      ( 1-cell-transitive-globular-type-Large-Transitive-Globular-Type x y) =
      is-transitive-1-cell-globular-type-is-transitive-Large-Globular-Type
        is-transitive-Large-Transitive-Globular-Type

    comp-2-cell-Large-Transitive-Globular-Type :
      {l1 l2 : Level}
      {x : 0-cell-Large-Transitive-Globular-Type l1}
      {y : 0-cell-Large-Transitive-Globular-Type l2}
      {f g h : 1-cell-Large-Transitive-Globular-Type x y} →
      2-cell-Large-Transitive-Globular-Type g h →
      2-cell-Large-Transitive-Globular-Type f g →
      2-cell-Large-Transitive-Globular-Type f h
    comp-2-cell-Large-Transitive-Globular-Type =
      comp-1-cell-Transitive-Globular-Type
        ( 1-cell-transitive-globular-type-Large-Transitive-Globular-Type _ _)

    2-cell-transitive-globular-type-Large-Transitive-Globular-Type :
      {l1 l2 : Level}
      {x : 0-cell-Large-Transitive-Globular-Type l1}
      {y : 0-cell-Large-Transitive-Globular-Type l2}
      (f g : 1-cell-Large-Transitive-Globular-Type x y) →
      Transitive-Globular-Type (β l1 l2) (β l1 l2)
    2-cell-transitive-globular-type-Large-Transitive-Globular-Type =
      1-cell-transitive-globular-type-Transitive-Globular-Type
        ( 1-cell-transitive-globular-type-Large-Transitive-Globular-Type _ _)

open Large-Transitive-Globular-Type public
```

### The predicate of being a transitive large globular structure

```agda
record
  is-transitive-large-globular-structure
  {α : Level → Level} {β : Level → Level → Level}
  {A : (l : Level) → UU (α l)}
  (G : large-globular-structure β A) : UUω
  where

  field
    comp-1-cell-is-transitive-large-globular-structure :
      {l1 l2 l3 : Level} {x : A l1} {y : A l2} {z : A l3} →
      1-cell-large-globular-structure G y z →
      1-cell-large-globular-structure G x y →
      1-cell-large-globular-structure G x z

    is-transitive-globular-structure-1-cell-is-transitive-large-globular-structure :
      {l1 l2 : Level} (x : A l1) (y : A l2) →
      is-transitive-globular-structure
        ( globular-structure-1-cell-large-globular-structure G x y)

open is-transitive-large-globular-structure public

module _
  {α : Level → Level} {β : Level → Level → Level}
  {A : (l : Level) → UU (α l)}
  {G : large-globular-structure β A}
  (r : is-transitive-large-globular-structure G)
  where

  comp-2-cell-is-transitive-large-globular-structure :
    {l1 l2 : Level} {x : A l1} {y : A l2}
    {f g h : 1-cell-large-globular-structure G x y} →
    2-cell-large-globular-structure G g h →
    2-cell-large-globular-structure G f g →
    2-cell-large-globular-structure G f h
  comp-2-cell-is-transitive-large-globular-structure {x = x} {y} =
    comp-1-cell-is-transitive-globular-structure
      ( is-transitive-globular-structure-1-cell-is-transitive-large-globular-structure
        ( r)
        ( x)
        ( y))

  comp-3-cell-is-transitive-large-globular-structure :
    {l1 l2 : Level} {x : A l1} {y : A l2}
    {f g : 1-cell-large-globular-structure G x y}
    {H K L : 2-cell-large-globular-structure G f g} →
    3-cell-large-globular-structure G K L →
    3-cell-large-globular-structure G H K →
    3-cell-large-globular-structure G H L
  comp-3-cell-is-transitive-large-globular-structure {x = x} {y} =
    comp-2-cell-is-transitive-globular-structure
      ( is-transitive-globular-structure-1-cell-is-transitive-large-globular-structure
        ( r)
        ( x)
        ( y))
```

### The type of transitive globular structures on a large type

```agda
record
  large-transitive-globular-structure
  {α : Level → Level} (β : Level → Level → Level) (A : (l : Level) → UU (α l))
  : UUω
  where

  field
    large-globular-structure-large-transitive-globular-structure :
      large-globular-structure β A

    is-transitive-large-globular-structure-large-transitive-globular-structure :
      is-transitive-large-globular-structure
        ( large-globular-structure-large-transitive-globular-structure)

open large-transitive-globular-structure public
```

### Large globular maps between large transitive globular types

```agda
module _
  {α1 α2 : Level → Level} {β1 β2 : Level → Level → Level} (γ : Level → Level)
  (G : Large-Transitive-Globular-Type α1 β1)
  (H : Large-Transitive-Globular-Type α2 β2)
  where

  large-globular-map-Large-Transitive-Globular-Type : UUω
  large-globular-map-Large-Transitive-Globular-Type =
    large-globular-map γ
      ( large-globular-type-Large-Transitive-Globular-Type G)
      ( large-globular-type-Large-Transitive-Globular-Type H)
```
