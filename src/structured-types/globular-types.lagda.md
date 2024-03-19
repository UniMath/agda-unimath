# Globular types

```agda
{-# OPTIONS --guardedness #-}

module structured-types.globular-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.iterated-dependent-product-types
open import foundation.telescopes
open import foundation.universe-levels
```

</details>

## Idea

A {{#concept "globular type" Agda=Globular-Type}} is a type
[equipped](foundation.structure.md) with a
[binary relation](foundation.binary-relations.md) valued in globular types.

Thus, a globular type consists of a base type `A` which is called the type of
_$0$-cells_, and for every pair of $0$-cells, a type of $1$-cells, and for every
pair of $1$-cells a type of $2$-cells, and so on _ad infinitum_.For every pair
of $n$-cells `s` and `t`, there is a type of $n+1$-cells _from `s` to `t`_, and
we say the $n+1$-cells have _source_ `s` and _target_ `t`.

The standard interpretation of the higher cells of a globular type is as arrows
from their source to their target. For instance, given two $0$-cells `x` and
`y`, two $1$-cells `f` and `g` from `x` to `y`, two $2$-cells `α` and `β` from
`f` to `g`, and a $3$-cell `H` from `α` to `β`, a common depiction would be

```text
            f
        ---------
      /  //   \\  \
    /   //  H  \\   ∨
   x  α|| ≡≡≡≡> ||β  y.
    \   \\     //   ∧
      \   V   V   /
        ---------
            g
```

## Definitions

### The structure of a globular type

```agda
record globular-structure {l : Level} (A : UU l) : UU (lsuc l)
  where
  coinductive
  field
    1-cell-globular-structure :
      (x y : A) → UU l
    globular-structure-1-cell-globular-structure :
      (x y : A) → globular-structure (1-cell-globular-structure x y)

open globular-structure public
```

#### Iterated projections for globular structures

```agda
module _
  {l : Level} {A : UU l} (G : globular-structure A)
  {x y : A} (f g : 1-cell-globular-structure G x y)
  where

  2-cell-globular-structure : UU l
  2-cell-globular-structure =
    1-cell-globular-structure
      ( globular-structure-1-cell-globular-structure G x y) f g

  globular-structure-2-cell-globular-structure :
    globular-structure 2-cell-globular-structure
  globular-structure-2-cell-globular-structure =
    globular-structure-1-cell-globular-structure
    ( globular-structure-1-cell-globular-structure G x y) f g

module _
  {l : Level} {A : UU l} (G : globular-structure A)
  {x y : A} {f g : 1-cell-globular-structure G x y}
  (p q : 2-cell-globular-structure G f g)
  where

  3-cell-globular-structure : UU l
  3-cell-globular-structure =
    1-cell-globular-structure
      ( globular-structure-2-cell-globular-structure G f g) p q

  globular-structure-3-cell-globular-structure :
    globular-structure 3-cell-globular-structure
  globular-structure-3-cell-globular-structure =
    globular-structure-1-cell-globular-structure
    ( globular-structure-2-cell-globular-structure G f g) p q

module _
  {l : Level} {A : UU l} (G : globular-structure A)
  {x y : A} {f g : 1-cell-globular-structure G x y}
  {p q : 2-cell-globular-structure G f g}
  (H K : 3-cell-globular-structure G p q)
  where

  4-cell-globular-structure : UU l
  4-cell-globular-structure =
    1-cell-globular-structure
      ( globular-structure-3-cell-globular-structure G p q) H K

  globular-structure-4-cell-globular-structure :
    globular-structure 4-cell-globular-structure
  globular-structure-4-cell-globular-structure =
    globular-structure-1-cell-globular-structure
    ( globular-structure-3-cell-globular-structure G p q) H K
```

### The type of globular types

```agda
Globular-Type : (l : Level) → UU (lsuc l)
Globular-Type l = Σ (UU l) globular-structure

module _
  {l : Level} (A : Globular-Type l)
  where

  0-cell-Globular-Type : UU l
  0-cell-Globular-Type = pr1 A

  globular-structure-0-cell-Globular-Type :
    globular-structure 0-cell-Globular-Type
  globular-structure-0-cell-Globular-Type = pr2 A

  1-cell-Globular-Type : (x y : 0-cell-Globular-Type) → UU l
  1-cell-Globular-Type =
    1-cell-globular-structure globular-structure-0-cell-Globular-Type

  globular-structure-1-cell-Globular-Type :
    (x y : 0-cell-Globular-Type) →
    globular-structure (1-cell-Globular-Type x y)
  globular-structure-1-cell-Globular-Type =
    globular-structure-1-cell-globular-structure
      ( globular-structure-0-cell-Globular-Type)

  globular-type-1-cell-Globular-Type :
    (x y : 0-cell-Globular-Type) → Globular-Type l
  globular-type-1-cell-Globular-Type x y =
    ( 1-cell-Globular-Type x y , globular-structure-1-cell-Globular-Type x y)

  2-cell-Globular-Type :
    {x y : 0-cell-Globular-Type} (f g : 1-cell-Globular-Type x y) → UU l
  2-cell-Globular-Type =
    2-cell-globular-structure globular-structure-0-cell-Globular-Type

  globular-structure-2-cell-Globular-Type :
    {x y : 0-cell-Globular-Type} (f g : 1-cell-Globular-Type x y) →
    globular-structure (2-cell-Globular-Type f g)
  globular-structure-2-cell-Globular-Type =
    globular-structure-2-cell-globular-structure
      ( globular-structure-0-cell-Globular-Type)

  globular-type-2-cell-Globular-Type :
    {x y : 0-cell-Globular-Type} (f g : 1-cell-Globular-Type x y) →
    Globular-Type l
  globular-type-2-cell-Globular-Type f g =
    ( 2-cell-Globular-Type f g , globular-structure-2-cell-Globular-Type f g)
```

## Examples

### The globular structure on a type given by its identity types

```agda
globular-structure-Id : {l : Level} (A : UU l) → globular-structure A
1-cell-globular-structure (globular-structure-Id A) x y =
  x ＝ y
globular-structure-1-cell-globular-structure (globular-structure-Id A) x y =
  globular-structure-Id (x ＝ y)
```
