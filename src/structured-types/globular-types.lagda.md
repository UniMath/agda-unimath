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

## Definition

### The structure of a globular type

```agda
record globular-structure {l : Level} (A : UU l) : UU (lsuc l)
  where
  coinductive
  field
    cells-globular-structure :
      (x y : A) → UU l
    higher-globular-structure :
      (x y : A) → globular-structure (cells-globular-structure x y)

open globular-structure public
```

### The type of globular types

```agda
Globular-Type : (l : Level) → UU (lsuc l)
Globular-Type l = Σ (UU l) globular-structure

module _
  {l : Level} (A : Globular-Type l)
  where

  0-cells-Globular-Type : UU l
  0-cells-Globular-Type = pr1 A

  globular-structure-0-cells-Globular-Type :
    globular-structure 0-cells-Globular-Type
  globular-structure-0-cells-Globular-Type = pr2 A

  1-cells-Globular-Type : (x y : 0-cells-Globular-Type) → UU l
  1-cells-Globular-Type =
    cells-globular-structure globular-structure-0-cells-Globular-Type

  globular-structure-1-cells-Globular-Type :
    (x y : 0-cells-Globular-Type) →
    globular-structure (1-cells-Globular-Type x y)
  globular-structure-1-cells-Globular-Type =
    higher-globular-structure globular-structure-0-cells-Globular-Type

  globular-type-1-cells-Globular-Type :
    (x y : 0-cells-Globular-Type) → Globular-Type l
  pr1 (globular-type-1-cells-Globular-Type x y) =
    1-cells-Globular-Type x y
  pr2 (globular-type-1-cells-Globular-Type x y) =
    globular-structure-1-cells-Globular-Type x y

  2-cells-Globular-Type :
    {x y : 0-cells-Globular-Type} (p q : 1-cells-Globular-Type x y) → UU l
  2-cells-Globular-Type {x} {y} =
    cells-globular-structure (globular-structure-1-cells-Globular-Type x y)
```

## Examples

### The globular structure on a type given by its identity types

```agda
globular-structure-Id : {l : Level} (A : UU l) → globular-structure A
cells-globular-structure (globular-structure-Id A) x y =
  x ＝ y
higher-globular-structure (globular-structure-Id A) x y =
  globular-structure-Id (x ＝ y)
```
