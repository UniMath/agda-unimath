# Large globular types

```agda
{-# OPTIONS --guardedness #-}

module structured-types.large-globular-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.iterated-dependent-product-types
open import foundation.telescopes
open import foundation.universe-levels

open import structured-types.globular-types
```

</details>

## Idea

A {{#concept "large globular type" Agda=Large-Globular-Type}} is a hierarchy of
types indexed by universe levels, [equipped](foundation.structure.md) with a
[large binary relation](foundation.large-binary-relations.md) valued in
[globular types](structured-types.globular-types.md).

Thus, a large globular type consists of a base collection of types indexed by
universe level `A` which is called the _$0$-cells_, and for every pair of
$0$-cells, there is a type of $1$-cells and so on. For every pair of $n$-cells,
there is a type of $n+1$-cells.

## Definition

### The structure of a globular type

```agda
record
  large-globular-structure
  {α : Level → Level} (β : Level → Level → Level) (A : (l : Level) → UU (α l))
  : UUω
  where
  coinductive
  field
    cells-large-globular-structure :
      {l1 l2 : Level} (x : A l1) (y : A l2) → UU (β l1 l2)
    higher-large-globular-structure :
      {l1 l2 : Level} (x : A l1) (y : A l2) →
      globular-structure (cells-large-globular-structure x y)

open large-globular-structure public
```

### The type of globular types

```agda
record
  Large-Globular-Type (α : Level → Level) (β : Level → Level → Level) : UUω
  where
  field
    0-cells-Large-Globular-Type :
      (l : Level) → UU (α l)
    globular-structure-0-cells-Large-Globular-Type :
      large-globular-structure β 0-cells-Large-Globular-Type

open Large-Globular-Type public

module _
  {α : Level → Level} {β : Level → Level → Level} (A : Large-Globular-Type α β)
  where

  1-cells-Large-Globular-Type :
    {l1 l2 : Level}
    (x : 0-cells-Large-Globular-Type A l1)
    (y : 0-cells-Large-Globular-Type A l2) →
    UU (β l1 l2)
  1-cells-Large-Globular-Type =
    cells-large-globular-structure
      ( globular-structure-0-cells-Large-Globular-Type A)

  globular-structure-1-cells-Large-Globular-Type :
    {l1 l2 : Level}
    (x : 0-cells-Large-Globular-Type A l1)
    (y : 0-cells-Large-Globular-Type A l2) →
    globular-structure (1-cells-Large-Globular-Type x y)
  globular-structure-1-cells-Large-Globular-Type =
    higher-large-globular-structure
      ( globular-structure-0-cells-Large-Globular-Type A)

  globular-type-1-cells-Large-Globular-Type :
    {l1 l2 : Level}
    (x : 0-cells-Large-Globular-Type A l1)
    (y : 0-cells-Large-Globular-Type A l2) →
    Globular-Type (β l1 l2)
  pr1 (globular-type-1-cells-Large-Globular-Type x y) =
    1-cells-Large-Globular-Type x y
  pr2 (globular-type-1-cells-Large-Globular-Type x y) =
    globular-structure-1-cells-Large-Globular-Type x y

  2-cells-Large-Globular-Type :
    {l1 l2 : Level}
    {x : 0-cells-Large-Globular-Type A l1}
    {y : 0-cells-Large-Globular-Type A l2}
    (p q : 1-cells-Large-Globular-Type x y) → UU (β l1 l2)
  2-cells-Large-Globular-Type {x = x} {y} =
    cells-globular-structure
      ( globular-structure-1-cells-Large-Globular-Type x y)
```
