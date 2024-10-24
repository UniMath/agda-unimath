# Large reflexive globular types

```agda
{-# OPTIONS --guardedness #-}

module structured-types.large-reflexive-globular-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.large-binary-relations
open import foundation.universe-levels

open import structured-types.globular-types
open import structured-types.large-globular-maps
open import structured-types.large-globular-types
open import structured-types.reflexive-globular-types
```

</details>

## Idea

A [large globular type](structured-types.large-globular-types.md) is
{{#concept "reflexive" Disambiguation="large globular type" Agda=is-reflexive-Large-Globular-Type}}
if every $n$-cell `x` comes with a choice of $(n+1)$-cell from `x` to `x`.

## Definition

### The predicate of being a reflexive large globular type

```agda
record
  is-reflexive-Large-Globular-Type
    {α : Level → Level} {β : Level → Level → Level}
    (A : Large-Globular-Type α β) :
    UUω
  where

  field
    refl-1-cell-is-reflexive-Large-Globular-Type :
      is-reflexive-Large-Relation
        ( 0-cell-Large-Globular-Type A)
        ( 1-cell-Large-Globular-Type A)

  field
    is-reflexive-1-cell-globular-type-is-reflexive-Large-Globular-Type :
      {l1 l2 : Level}
      {x : 0-cell-Large-Globular-Type A l1}
      {y : 0-cell-Large-Globular-Type A l2} →
      is-reflexive-Globular-Type
        ( 1-cell-globular-type-Large-Globular-Type A x y)

  refl-2-cell-is-reflexive-Large-Globular-Type :
    {l1 l2 : Level}
    {x : 0-cell-Large-Globular-Type A l1}
    {y : 0-cell-Large-Globular-Type A l2} →
    is-reflexive (2-cell-Large-Globular-Type A {x = x} {y = y})
  refl-2-cell-is-reflexive-Large-Globular-Type =
    is-reflexive-1-cell-is-reflexive-Globular-Type
      ( is-reflexive-1-cell-globular-type-is-reflexive-Large-Globular-Type)

  is-reflexive-2-cell-globular-type-is-reflexive-Large-Globular-Type :
    {l1 l2 : Level}
    {x : 0-cell-Large-Globular-Type A l1}
    {y : 0-cell-Large-Globular-Type A l2}
    {f g : 1-cell-Large-Globular-Type A x y} →
    is-reflexive-Globular-Type
      ( 2-cell-globular-type-Large-Globular-Type A f g)
  is-reflexive-2-cell-globular-type-is-reflexive-Large-Globular-Type =
    is-reflexive-1-cell-globular-type-is-reflexive-Globular-Type
      is-reflexive-1-cell-globular-type-is-reflexive-Large-Globular-Type

  refl-3-cell-is-reflexive-Large-Globular-Type :
    {l1 l2 : Level}
    {x : 0-cell-Large-Globular-Type A l1}
    {y : 0-cell-Large-Globular-Type A l2}
    {f g : 1-cell-Large-Globular-Type A x y} →
    is-reflexive (3-cell-Large-Globular-Type A {f = f} {g = g})
  refl-3-cell-is-reflexive-Large-Globular-Type =
    is-reflexive-2-cell-is-reflexive-Globular-Type
      ( is-reflexive-1-cell-globular-type-is-reflexive-Large-Globular-Type)

  is-reflexive-3-cell-globular-type-is-reflexive-Large-Globular-Type :
    {l1 l2 : Level}
    {x : 0-cell-Large-Globular-Type A l1}
    {y : 0-cell-Large-Globular-Type A l2}
    {f g : 1-cell-Large-Globular-Type A x y}
    {s t : 2-cell-Large-Globular-Type A f g} →
    is-reflexive-Globular-Type
      ( 3-cell-globular-type-Large-Globular-Type A s t)
  is-reflexive-3-cell-globular-type-is-reflexive-Large-Globular-Type =
    is-reflexive-2-cell-globular-type-is-reflexive-Globular-Type
      is-reflexive-1-cell-globular-type-is-reflexive-Large-Globular-Type

open is-reflexive-Large-Globular-Type public
```

### Large reflexive globular types

```agda
record
  Large-Reflexive-Globular-Type
    ( α : Level → Level) (β : Level → Level → Level) : UUω
  where
```

- The underlying large globular type of a large reflexive globular type

```agda
  field
    large-globular-type-Large-Reflexive-Globular-Type :
      Large-Globular-Type α β

  0-cell-Large-Reflexive-Globular-Type : (l : Level) → UU (α l)
  0-cell-Large-Reflexive-Globular-Type =
    0-cell-Large-Globular-Type
      large-globular-type-Large-Reflexive-Globular-Type

  1-cell-Large-Reflexive-Globular-Type :
    {l1 l2 : Level}
    (x : 0-cell-Large-Reflexive-Globular-Type l1)
    (y : 0-cell-Large-Reflexive-Globular-Type l2) →
    UU (β l1 l2)
  1-cell-Large-Reflexive-Globular-Type =
    1-cell-Large-Globular-Type
      large-globular-type-Large-Reflexive-Globular-Type

  2-cell-Large-Reflexive-Globular-Type :
    {l1 l2 : Level}
    {x : 0-cell-Large-Reflexive-Globular-Type l1}
    {y : 0-cell-Large-Reflexive-Globular-Type l2}
    (f g : 1-cell-Large-Reflexive-Globular-Type x y) → UU (β l1 l2)
  2-cell-Large-Reflexive-Globular-Type =
    2-cell-Large-Globular-Type
      large-globular-type-Large-Reflexive-Globular-Type

  3-cell-Large-Reflexive-Globular-Type :
    {l1 l2 : Level}
    {x : 0-cell-Large-Reflexive-Globular-Type l1}
    {y : 0-cell-Large-Reflexive-Globular-Type l2}
    {f g : 1-cell-Large-Reflexive-Globular-Type x y}
    (s t : 2-cell-Large-Reflexive-Globular-Type f g) → UU (β l1 l2)
  3-cell-Large-Reflexive-Globular-Type =
    3-cell-Large-Globular-Type
      large-globular-type-Large-Reflexive-Globular-Type

  4-cell-Large-Reflexive-Globular-Type :
    {l1 l2 : Level}
    {x : 0-cell-Large-Reflexive-Globular-Type l1}
    {y : 0-cell-Large-Reflexive-Globular-Type l2}
    {f g : 1-cell-Large-Reflexive-Globular-Type x y}
    {s t : 2-cell-Large-Reflexive-Globular-Type f g}
    (u v : 3-cell-Large-Reflexive-Globular-Type s t) → UU (β l1 l2)
  4-cell-Large-Reflexive-Globular-Type =
    4-cell-Large-Globular-Type
      large-globular-type-Large-Reflexive-Globular-Type

  5-cell-Large-Reflexive-Globular-Type :
    {l1 l2 : Level}
    {x : 0-cell-Large-Reflexive-Globular-Type l1}
    {y : 0-cell-Large-Reflexive-Globular-Type l2}
    {f g : 1-cell-Large-Reflexive-Globular-Type x y}
    {s t : 2-cell-Large-Reflexive-Globular-Type f g}
    {u v : 3-cell-Large-Reflexive-Globular-Type s t}
    (a b : 4-cell-Large-Reflexive-Globular-Type u v) → UU (β l1 l2)
  5-cell-Large-Reflexive-Globular-Type =
    5-cell-Large-Globular-Type
      large-globular-type-Large-Reflexive-Globular-Type

  1-cell-globular-type-Large-Reflexive-Globular-Type :
    {l1 l2 : Level}
    (x : 0-cell-Large-Reflexive-Globular-Type l1)
    (y : 0-cell-Large-Reflexive-Globular-Type l2) →
    Globular-Type (β l1 l2) (β l1 l2)
  1-cell-globular-type-Large-Reflexive-Globular-Type =
    1-cell-globular-type-Large-Globular-Type
      large-globular-type-Large-Reflexive-Globular-Type

  2-cell-globular-type-Large-Reflexive-Globular-Type :
    {l1 l2 : Level}
    {x : 0-cell-Large-Reflexive-Globular-Type l1}
    {y : 0-cell-Large-Reflexive-Globular-Type l2}
    (f g : 1-cell-Large-Reflexive-Globular-Type x y) →
    Globular-Type (β l1 l2) (β l1 l2)
  2-cell-globular-type-Large-Reflexive-Globular-Type =
    2-cell-globular-type-Large-Globular-Type
      large-globular-type-Large-Reflexive-Globular-Type

  3-cell-globular-type-Large-Reflexive-Globular-Type :
    {l1 l2 : Level}
    {x : 0-cell-Large-Reflexive-Globular-Type l1}
    {y : 0-cell-Large-Reflexive-Globular-Type l2}
    {f g : 1-cell-Large-Reflexive-Globular-Type x y}
    (s t : 2-cell-Large-Reflexive-Globular-Type f g) →
    Globular-Type (β l1 l2) (β l1 l2)
  3-cell-globular-type-Large-Reflexive-Globular-Type =
    3-cell-globular-type-Large-Globular-Type
      large-globular-type-Large-Reflexive-Globular-Type

  4-cell-globular-type-Large-Reflexive-Globular-Type :
    {l1 l2 : Level}
    {x : 0-cell-Large-Reflexive-Globular-Type l1}
    {y : 0-cell-Large-Reflexive-Globular-Type l2}
    {f g : 1-cell-Large-Reflexive-Globular-Type x y}
    {s t : 2-cell-Large-Reflexive-Globular-Type f g}
    (u v : 3-cell-Large-Reflexive-Globular-Type s t) →
    Globular-Type (β l1 l2) (β l1 l2)
  4-cell-globular-type-Large-Reflexive-Globular-Type =
    4-cell-globular-type-Large-Globular-Type
      large-globular-type-Large-Reflexive-Globular-Type

  5-cell-globular-type-Large-Reflexive-Globular-Type :
    {l1 l2 : Level}
    {x : 0-cell-Large-Reflexive-Globular-Type l1}
    {y : 0-cell-Large-Reflexive-Globular-Type l2}
    {f g : 1-cell-Large-Reflexive-Globular-Type x y}
    {s t : 2-cell-Large-Reflexive-Globular-Type f g}
    {u v : 3-cell-Large-Reflexive-Globular-Type s t}
    (a b : 4-cell-Large-Reflexive-Globular-Type u v) →
    Globular-Type (β l1 l2) (β l1 l2)
  5-cell-globular-type-Large-Reflexive-Globular-Type =
    5-cell-globular-type-Large-Globular-Type
      large-globular-type-Large-Reflexive-Globular-Type

  globular-structure-1-cell-Large-Reflexive-Globular-Type :
    {l1 l2 : Level}
    (x : 0-cell-Large-Reflexive-Globular-Type l1)
    (y : 0-cell-Large-Reflexive-Globular-Type l2) →
    globular-structure (β l1 l2) (1-cell-Large-Reflexive-Globular-Type x y)
  globular-structure-1-cell-Large-Reflexive-Globular-Type =
    globular-structure-1-cell-Large-Globular-Type
      large-globular-type-Large-Reflexive-Globular-Type

  globular-structure-2-cell-Large-Reflexive-Globular-Type :
    {l1 l2 : Level}
    {x : 0-cell-Large-Reflexive-Globular-Type l1}
    {y : 0-cell-Large-Reflexive-Globular-Type l2}
    (f g : 1-cell-Large-Reflexive-Globular-Type x y) →
    globular-structure (β l1 l2) (2-cell-Large-Reflexive-Globular-Type f g)
  globular-structure-2-cell-Large-Reflexive-Globular-Type =
    globular-structure-2-cell-Large-Globular-Type
      large-globular-type-Large-Reflexive-Globular-Type

  globular-structure-3-cell-Large-Reflexive-Globular-Type :
    {l1 l2 : Level}
    {x : 0-cell-Large-Reflexive-Globular-Type l1}
    {y : 0-cell-Large-Reflexive-Globular-Type l2}
    {f g : 1-cell-Large-Reflexive-Globular-Type x y}
    (s t : 2-cell-Large-Reflexive-Globular-Type f g) →
    globular-structure (β l1 l2) (3-cell-Large-Reflexive-Globular-Type s t)
  globular-structure-3-cell-Large-Reflexive-Globular-Type =
    globular-structure-3-cell-Large-Globular-Type
      large-globular-type-Large-Reflexive-Globular-Type

  globular-structure-4-cell-Large-Reflexive-Globular-Type :
    {l1 l2 : Level}
    {x : 0-cell-Large-Reflexive-Globular-Type l1}
    {y : 0-cell-Large-Reflexive-Globular-Type l2}
    {f g : 1-cell-Large-Reflexive-Globular-Type x y}
    {s t : 2-cell-Large-Reflexive-Globular-Type f g}
    (u v : 3-cell-Large-Reflexive-Globular-Type s t) →
    globular-structure (β l1 l2) (4-cell-Large-Reflexive-Globular-Type u v)
  globular-structure-4-cell-Large-Reflexive-Globular-Type =
    globular-structure-4-cell-Large-Globular-Type
      large-globular-type-Large-Reflexive-Globular-Type

  large-globular-structure-0-cell-Large-Reflexive-Globular-Type :
    large-globular-structure β (0-cell-Large-Reflexive-Globular-Type)
  large-globular-structure-0-cell-Large-Reflexive-Globular-Type =
    large-globular-structure-0-cell-Large-Globular-Type
      large-globular-type-Large-Reflexive-Globular-Type
```

- The reflexivity structure of a large reflexive globular type

```agda
  field
    is-reflexive-Large-Reflexive-Globular-Type :
      is-reflexive-Large-Globular-Type
        large-globular-type-Large-Reflexive-Globular-Type

  refl-1-cell-Large-Reflexive-Globular-Type :
    {l1 : Level} {x : 0-cell-Large-Reflexive-Globular-Type l1} →
    1-cell-Large-Reflexive-Globular-Type x x
  refl-1-cell-Large-Reflexive-Globular-Type =
    refl-1-cell-is-reflexive-Large-Globular-Type
      ( is-reflexive-Large-Reflexive-Globular-Type)
      ( _)

  is-reflexive-1-cell-globular-type-Large-Reflexive-Globular-Type :
    {l1 l2 : Level}
    {x : 0-cell-Large-Reflexive-Globular-Type l1}
    {y : 0-cell-Large-Reflexive-Globular-Type l2} →
    is-reflexive-Globular-Type
      ( 1-cell-globular-type-Large-Reflexive-Globular-Type x y)
  is-reflexive-1-cell-globular-type-Large-Reflexive-Globular-Type =
    is-reflexive-1-cell-globular-type-is-reflexive-Large-Globular-Type
      is-reflexive-Large-Reflexive-Globular-Type

  1-cell-reflexive-globular-type-Large-Reflexive-Globular-Type :
    {l1 l2 : Level}
    (x : 0-cell-Large-Reflexive-Globular-Type l1)
    (y : 0-cell-Large-Reflexive-Globular-Type l2) →
    Reflexive-Globular-Type (β l1 l2) (β l1 l2)
  globular-type-Reflexive-Globular-Type
    ( 1-cell-reflexive-globular-type-Large-Reflexive-Globular-Type x y) =
    1-cell-globular-type-Large-Reflexive-Globular-Type x y
  refl-Reflexive-Globular-Type
    ( 1-cell-reflexive-globular-type-Large-Reflexive-Globular-Type x y) =
    is-reflexive-1-cell-globular-type-Large-Reflexive-Globular-Type

  refl-2-cell-Large-Reflexive-Globular-Type :
    {l1 l2 : Level}
    {x : 0-cell-Large-Reflexive-Globular-Type l1}
    {y : 0-cell-Large-Reflexive-Globular-Type l2}
    {f : 1-cell-Large-Reflexive-Globular-Type x y} →
    2-cell-Large-Reflexive-Globular-Type f f
  refl-2-cell-Large-Reflexive-Globular-Type =
    refl-2-cell-is-reflexive-Large-Globular-Type
      ( is-reflexive-Large-Reflexive-Globular-Type)
      ( _)

  is-reflexive-2-cell-globular-type-Large-Reflexive-Globular-Type :
    {l1 l2 : Level}
    {x : 0-cell-Large-Reflexive-Globular-Type l1}
    {y : 0-cell-Large-Reflexive-Globular-Type l2}
    {f g : 1-cell-Large-Reflexive-Globular-Type x y} →
    is-reflexive-Globular-Type
      ( 2-cell-globular-type-Large-Reflexive-Globular-Type f g)
  is-reflexive-2-cell-globular-type-Large-Reflexive-Globular-Type =
    is-reflexive-2-cell-globular-type-is-reflexive-Large-Globular-Type
      is-reflexive-Large-Reflexive-Globular-Type

  2-cell-reflexive-globular-type-Large-Reflexive-Globular-Type :
    {l1 l2 : Level}
    {x : 0-cell-Large-Reflexive-Globular-Type l1}
    {y : 0-cell-Large-Reflexive-Globular-Type l2}
    (f g : 1-cell-Large-Reflexive-Globular-Type x y) →
    Reflexive-Globular-Type (β l1 l2) (β l1 l2)
  globular-type-Reflexive-Globular-Type
    ( 2-cell-reflexive-globular-type-Large-Reflexive-Globular-Type f g) =
    2-cell-globular-type-Large-Reflexive-Globular-Type f g
  refl-Reflexive-Globular-Type
    ( 2-cell-reflexive-globular-type-Large-Reflexive-Globular-Type f g) =
    is-reflexive-2-cell-globular-type-Large-Reflexive-Globular-Type

open Large-Reflexive-Globular-Type public
```

### Large globular maps between large reflexive globular types

```agda
module _
  {α1 α2 : Level → Level} {β1 β2 : Level → Level → Level} (γ : Level → Level)
  (G : Large-Reflexive-Globular-Type α1 β1)
  (H : Large-Reflexive-Globular-Type α2 β2)
  where

  large-globular-map-Large-Reflexive-Globular-Type : UUω
  large-globular-map-Large-Reflexive-Globular-Type =
    large-globular-map γ
      ( large-globular-type-Large-Reflexive-Globular-Type G)
      ( large-globular-type-Large-Reflexive-Globular-Type H)
```
