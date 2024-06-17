# Large transitive globular types

```agda
{-# OPTIONS --guardedness #-}

module structured-types.large-transitive-globular-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import structured-types.large-globular-types
open import structured-types.transitive-globular-types
```

</details>

## Idea

A
{{#concept "large transitive globular type" Agda=Large-Transitive-Globular-Type}}
is a [large globular type](structured-types.large-globular-types.md) `A`
[equipped](foundation.structure.md) with a binary operator

```text
  - * - : (𝑛+1)-Cell A y z → (𝑛+1)-Cell A x y → (𝑛+1)-Cell A x z
```

at every level $n$.

## Definition

### The structure transitivitiy on a large globular type

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

### The type of large transitive globular types

```agda
record
  Large-Transitive-Globular-Type
  (α : Level → Level) (β : Level → Level → Level) : UUω
  where

  field
    0-cell-Large-Transitive-Globular-Type : (l : Level) → UU (α l)

    transitive-globular-structure-0-cell-Large-Transitive-Globular-Type :
      large-transitive-globular-structure
        ( β)
        ( 0-cell-Large-Transitive-Globular-Type)

open Large-Transitive-Globular-Type public
```
