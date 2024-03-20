# Large ∞-magmoids

```agda
{-# OPTIONS --guardedness #-}

module structured-types.large-infinity-magmoids where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import structured-types.infinity-magmoids
open import structured-types.large-globular-types
```

</details>

## Idea

A {{#concept "large $∞$-magmoid" Agda=Large-∞-Magmoid}} is a
[large globular type](structured-types.large-globular-types.md) `A`
[equipped](foundation.structure.md) with a binary operator

```text
  - * - : (𝑛+1)-Cell A y z → (𝑛+1)-Cell A x y → (𝑛+1)-Cell A x z
```

at every level $n$.

## Definition

### The structure of a large $∞$-magmoid on a large globular type

```agda
record
  is-∞-magmoid-large-globular-structure
  {α : Level → Level} {β : Level → Level → Level}
  {A : (l : Level) → UU (α l)}
  (G : large-globular-structure β A) : UUω
  where

  field
    comp-1-cell-is-∞-magmoid-large-globular-structure :
      {l1 l2 l3 : Level} {x : A l1} {y : A l2} {z : A l3} →
      1-cell-large-globular-structure G y z →
      1-cell-large-globular-structure G x y →
      1-cell-large-globular-structure G x z

    is-∞-magmoid-globular-structure-1-cell-is-∞-magmoid-large-globular-structure :
      {l1 l2 : Level} (x : A l1) (y : A l2) →
      is-∞-magmoid-globular-structure
        ( globular-structure-1-cell-large-globular-structure G x y)

open is-∞-magmoid-large-globular-structure public

module _
  {α : Level → Level} {β : Level → Level → Level}
  {A : (l : Level) → UU (α l)}
  {G : large-globular-structure β A}
  (r : is-∞-magmoid-large-globular-structure G)
  where

  comp-2-cell-is-∞-magmoid-large-globular-structure :
    {l1 l2 : Level} {x : A l1} {y : A l2}
    {f g h : 1-cell-large-globular-structure G x y} →
    2-cell-large-globular-structure G g h →
    2-cell-large-globular-structure G f g →
    2-cell-large-globular-structure G f h
  comp-2-cell-is-∞-magmoid-large-globular-structure {x = x} {y} =
    comp-1-cell-is-∞-magmoid-globular-structure
      ( is-∞-magmoid-globular-structure-1-cell-is-∞-magmoid-large-globular-structure
        ( r)
        ( x)
        ( y))
```

### The type of $∞$-magmoid structures on a large type

```agda
record
  is-large-∞-magmoid
  {α : Level → Level} (β : Level → Level → Level) (A : (l : Level) → UU (α l))
  : UUω
  where

  field
    large-globular-structure-is-large-∞-magmoid :
      large-globular-structure β A

    is-∞-magmoid-large-globular-structure-is-large-∞-magmoid :
      is-∞-magmoid-large-globular-structure
        ( large-globular-structure-is-large-∞-magmoid)

open is-large-∞-magmoid public
```

### The type of $∞$-magmoids

```agda
record
  Large-∞-Magmoid (α : Level → Level) (β : Level → Level → Level) : UUω
  where

  field
    0-cell-Large-∞-Magmoid : (l : Level) → UU (α l)

    is-large-∞-magmoid-0-cell-Large-∞-Magmoid :
      is-large-∞-magmoid β 0-cell-Large-∞-Magmoid

open Large-∞-Magmoid public
```
