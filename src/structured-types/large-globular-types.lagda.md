# Large globular types

```agda
{-# OPTIONS --guardedness #-}

module structured-types.large-globular-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import structured-types.globular-types
```

</details>

## Idea

A {{#concept "large globular type" Agda=Large-Globular-Type}} is a hierarchy of
types indexed by universe levels, [equipped](foundation.structure.md) with a
[large binary relation](foundation.large-binary-relations.md) valued in
[globular types](structured-types.globular-types.md).

Thus, a large globular type consists of a base hierarchy of types indexed by
universe levels `A` called the _$0$-cells_, and for every pair of $0$-cells, a
type of $1$-cells, and for every pair of $1$-cells a type of $2$-cells, and so
on _ad infinitum_. For every pair of $n$-cells `s` and `t`, there is a type of
$(n+1)$-cells _from `s` to `t`_, and we say the $(n+1)$-cells have _source_ `s`
and _target_ `t`.

The standard interpretation of the higher cells of a globular type is as arrows
from their source to their target. For instance, given two $0$-cells `x` and
`y`, two $1$-cells `f` and `g` from `x` to `y`, two $2$-cells `H` and `K` from
`f` to `g`, and a $3$-cell `α` from `H` to `K`, a common depiction would be

```text
            f
       -----------
     /  //     \\  \
    /  //   α   \\  ∨
   x  H|| ≡≡≡≡> ||K  y.
    \  \\       //  ∧
     \  V       V  /
       -----------
            g
```

## Definitions

### The structure of a large globular type

```agda
record
  large-globular-structure
  {α : Level → Level} (β : Level → Level → Level) (A : (l : Level) → UU (α l))
  : UUω
  where
  field
    1-cell-large-globular-structure :
      {l1 l2 : Level} (x : A l1) (y : A l2) → UU (β l1 l2)
    globular-structure-1-cell-large-globular-structure :
      {l1 l2 : Level} (x : A l1) (y : A l2) →
      globular-structure (β l1 l2) (1-cell-large-globular-structure x y)

open large-globular-structure public
```

#### Iterated projections for large globular structures

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  {A : (l : Level) → UU (α l)}
  (G : large-globular-structure β A)
  {l1 l2 : Level} {x : A l1} {y : A l2}
  (f g : 1-cell-large-globular-structure G x y)
  where

  2-cell-large-globular-structure : UU (β l1 l2)
  2-cell-large-globular-structure =
    1-cell-globular-structure
      ( globular-structure-1-cell-large-globular-structure G x y) f g

  globular-structure-2-cell-large-globular-structure :
    globular-structure (β l1 l2) 2-cell-large-globular-structure
  globular-structure-2-cell-large-globular-structure =
    globular-structure-1-cell-globular-structure
      ( globular-structure-1-cell-large-globular-structure G x y) f g

module _
  {α : Level → Level} {β : Level → Level → Level}
  {A : (l : Level) → UU (α l)}
  (G : large-globular-structure β A)
  {l1 l2 : Level} {x : A l1} {y : A l2}
  {f g : 1-cell-large-globular-structure G x y}
  (p q : 2-cell-large-globular-structure G f g)
  where

  3-cell-large-globular-structure : UU (β l1 l2)
  3-cell-large-globular-structure =
    1-cell-globular-structure
      ( globular-structure-2-cell-large-globular-structure G f g) p q

  globular-structure-3-cell-large-globular-structure :
    globular-structure (β l1 l2) 3-cell-large-globular-structure
  globular-structure-3-cell-large-globular-structure =
    globular-structure-1-cell-globular-structure
      ( globular-structure-2-cell-large-globular-structure G f g) p q

module _
  {α : Level → Level} {β : Level → Level → Level}
  {A : (l : Level) → UU (α l)}
  (G : large-globular-structure β A)
  {l1 l2 : Level} {x : A l1} {y : A l2}
  {f g : 1-cell-large-globular-structure G x y}
  {p q : 2-cell-large-globular-structure G f g}
  (H K : 3-cell-large-globular-structure G p q)
  where

  4-cell-large-globular-structure : UU (β l1 l2)
  4-cell-large-globular-structure =
    1-cell-globular-structure
      ( globular-structure-3-cell-large-globular-structure G p q) H K

  globular-structure-4-cell-large-globular-structure :
    globular-structure (β l1 l2) 4-cell-large-globular-structure
  globular-structure-4-cell-large-globular-structure =
    globular-structure-1-cell-globular-structure
      ( globular-structure-3-cell-large-globular-structure G p q) H K
```

### The type of large globular types

```agda
record
  Large-Globular-Type (α : Level → Level) (β : Level → Level → Level) : UUω
  where
  field
    0-cell-Large-Globular-Type :
      (l : Level) → UU (α l)
    globular-structure-0-cell-Large-Globular-Type :
      large-globular-structure β 0-cell-Large-Globular-Type

open Large-Globular-Type public

module _
  {α : Level → Level} {β : Level → Level → Level} (A : Large-Globular-Type α β)
  where

  1-cell-Large-Globular-Type :
    {l1 l2 : Level}
    (x : 0-cell-Large-Globular-Type A l1)
    (y : 0-cell-Large-Globular-Type A l2) →
    UU (β l1 l2)
  1-cell-Large-Globular-Type =
    1-cell-large-globular-structure
      ( globular-structure-0-cell-Large-Globular-Type A)

  globular-structure-1-cell-Large-Globular-Type :
    {l1 l2 : Level}
    (x : 0-cell-Large-Globular-Type A l1)
    (y : 0-cell-Large-Globular-Type A l2) →
    globular-structure (β l1 l2) (1-cell-Large-Globular-Type x y)
  globular-structure-1-cell-Large-Globular-Type =
    globular-structure-1-cell-large-globular-structure
      ( globular-structure-0-cell-Large-Globular-Type A)

  globular-type-1-cell-Large-Globular-Type :
    {l1 l2 : Level}
    (x : 0-cell-Large-Globular-Type A l1)
    (y : 0-cell-Large-Globular-Type A l2) →
    Globular-Type (β l1 l2) (β l1 l2)
  globular-type-1-cell-Large-Globular-Type x y =
    ( 1-cell-Large-Globular-Type x y ,
      globular-structure-1-cell-Large-Globular-Type x y)

  2-cell-Large-Globular-Type :
    {l1 l2 : Level}
    {x : 0-cell-Large-Globular-Type A l1}
    {y : 0-cell-Large-Globular-Type A l2}
    (p q : 1-cell-Large-Globular-Type x y) → UU (β l1 l2)
  2-cell-Large-Globular-Type {x = x} {y} =
    1-cell-globular-structure
      ( globular-structure-1-cell-Large-Globular-Type x y)

  globular-structure-2-cell-Large-Globular-Type :
    {l1 l2 : Level}
    {x : 0-cell-Large-Globular-Type A l1}
    {y : 0-cell-Large-Globular-Type A l2}
    (f g : 1-cell-Large-Globular-Type x y) →
    globular-structure (β l1 l2) (2-cell-Large-Globular-Type f g)
  globular-structure-2-cell-Large-Globular-Type =
    globular-structure-2-cell-large-globular-structure
      ( globular-structure-0-cell-Large-Globular-Type A)

  globular-type-2-cell-Large-Globular-Type :
    {l1 l2 : Level}
    {x : 0-cell-Large-Globular-Type A l1}
    {y : 0-cell-Large-Globular-Type A l2}
    (f g : 1-cell-Large-Globular-Type x y) →
    Globular-Type (β l1 l2) (β l1 l2)
  globular-type-2-cell-Large-Globular-Type f g =
    ( 2-cell-Large-Globular-Type f g ,
      globular-structure-2-cell-Large-Globular-Type f g)

  3-cell-Large-Globular-Type :
    {l1 l2 : Level}
    {x : 0-cell-Large-Globular-Type A l1}
    {y : 0-cell-Large-Globular-Type A l2}
    {p q : 1-cell-Large-Globular-Type x y}
    (H K : 2-cell-Large-Globular-Type p q) → UU (β l1 l2)
  3-cell-Large-Globular-Type {x = x} {y} =
    2-cell-globular-structure
      ( globular-structure-1-cell-Large-Globular-Type x y)
```
