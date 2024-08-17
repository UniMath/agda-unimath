# Globular types

```agda
{-# OPTIONS --guardedness #-}

module structured-types.globular-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels
```

</details>

## Idea

A {{#concept "globular type" Agda=Globular-Type}} is a type equipped with a
[binary relation](foundation.binary-relations.md) valued in globular types.

Thus, a globular type consists of a base type `A` which is called the type of
$0$-cells, and for every pair of $0$-cells, a type of $1$-cells, and for every
pair of $1$-cells a type of $2$-cells, and so on _ad infinitum_. For every pair
of $n$-cells `s` and `t`, there is a type of $(n+1)$-cells _from `s` to `t`_,
and we say the $(n+1)$-cells have _source_ `s` and _target_ `t`.

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

We follow the conventional approach of the library and start by defining the
globular [structure](foundation.structure.md) on a type, and then define a
globular type to be a type equipped with such structure. Note that we could
equivalently have started by defining globular types, and then define globular
structures on a type as binary families of globular types on it, but this is a
special property of globular types.

## Definitions

### The structure of a globular type

**Comment.** The choice to add a second universe level in the definition of a
globular structure may seem rather arbitrary, but makes the concept applicable
in particular extra cases that are of use to us when working with
[large globular structures](structured-types.large-globular-types.md).

```agda
record
  globular-structure {l1 : Level} (l2 : Level) (A : UU l1) : UU (l1 ⊔ lsuc l2)
  where
  coinductive
  field
    1-cell-globular-structure :
      (x y : A) → UU l2
    globular-structure-1-cell-globular-structure :
      (x y : A) → globular-structure l2 (1-cell-globular-structure x y)

open globular-structure public
```

#### Iterated projections for globular structures

```agda
module _
  {l1 l2 : Level} {A : UU l1} (G : globular-structure l2 A)
  {x y : A} (f g : 1-cell-globular-structure G x y)
  where

  2-cell-globular-structure : UU l2
  2-cell-globular-structure =
    1-cell-globular-structure
      ( globular-structure-1-cell-globular-structure G x y) f g

  globular-structure-2-cell-globular-structure :
    globular-structure l2 2-cell-globular-structure
  globular-structure-2-cell-globular-structure =
    globular-structure-1-cell-globular-structure
      ( globular-structure-1-cell-globular-structure G x y) f g

module _
  {l1 l2 : Level} {A : UU l1} (G : globular-structure l2 A)
  {x y : A} {f g : 1-cell-globular-structure G x y}
  (p q : 2-cell-globular-structure G f g)
  where

  3-cell-globular-structure : UU l2
  3-cell-globular-structure =
    1-cell-globular-structure
      ( globular-structure-2-cell-globular-structure G f g) p q

  globular-structure-3-cell-globular-structure :
    globular-structure l2 3-cell-globular-structure
  globular-structure-3-cell-globular-structure =
    globular-structure-1-cell-globular-structure
      ( globular-structure-2-cell-globular-structure G f g) p q

module _
  {l1 l2 : Level} {A : UU l1} (G : globular-structure l2 A)
  {x y : A} {f g : 1-cell-globular-structure G x y}
  {p q : 2-cell-globular-structure G f g}
  (H K : 3-cell-globular-structure G p q)
  where

  4-cell-globular-structure : UU l2
  4-cell-globular-structure =
    1-cell-globular-structure
      ( globular-structure-3-cell-globular-structure G p q) H K

  globular-structure-4-cell-globular-structure :
    globular-structure l2 4-cell-globular-structure
  globular-structure-4-cell-globular-structure =
    globular-structure-1-cell-globular-structure
      ( globular-structure-3-cell-globular-structure G p q) H K
```

### The type of globular types

```agda
Globular-Type : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Globular-Type l1 l2 = Σ (UU l1) (globular-structure l2)

module _
  {l1 l2 : Level} (A : Globular-Type l1 l2)
  where

  0-cell-Globular-Type : UU l1
  0-cell-Globular-Type = pr1 A

  globular-structure-0-cell-Globular-Type :
    globular-structure l2 0-cell-Globular-Type
  globular-structure-0-cell-Globular-Type = pr2 A

  1-cell-Globular-Type : (x y : 0-cell-Globular-Type) → UU l2
  1-cell-Globular-Type =
    1-cell-globular-structure globular-structure-0-cell-Globular-Type

  globular-structure-1-cell-Globular-Type :
    (x y : 0-cell-Globular-Type) →
    globular-structure l2 (1-cell-Globular-Type x y)
  globular-structure-1-cell-Globular-Type =
    globular-structure-1-cell-globular-structure
      ( globular-structure-0-cell-Globular-Type)

  globular-type-1-cell-Globular-Type :
    (x y : 0-cell-Globular-Type) → Globular-Type l2 l2
  globular-type-1-cell-Globular-Type x y =
    ( 1-cell-Globular-Type x y , globular-structure-1-cell-Globular-Type x y)

  2-cell-Globular-Type :
    {x y : 0-cell-Globular-Type} (f g : 1-cell-Globular-Type x y) → UU l2
  2-cell-Globular-Type =
    2-cell-globular-structure globular-structure-0-cell-Globular-Type

  globular-structure-2-cell-Globular-Type :
    {x y : 0-cell-Globular-Type} (f g : 1-cell-Globular-Type x y) →
    globular-structure l2 (2-cell-Globular-Type f g)
  globular-structure-2-cell-Globular-Type =
    globular-structure-2-cell-globular-structure
      ( globular-structure-0-cell-Globular-Type)

  globular-type-2-cell-Globular-Type :
    {x y : 0-cell-Globular-Type} (f g : 1-cell-Globular-Type x y) →
    Globular-Type l2 l2
  globular-type-2-cell-Globular-Type f g =
    ( 2-cell-Globular-Type f g , globular-structure-2-cell-Globular-Type f g)

  3-cell-Globular-Type :
    {x y : 0-cell-Globular-Type} {f g : 1-cell-Globular-Type x y}
    (H K : 2-cell-Globular-Type f g) → UU l2
  3-cell-Globular-Type =
    3-cell-globular-structure globular-structure-0-cell-Globular-Type

  4-cell-Globular-Type :
    {x y : 0-cell-Globular-Type} {f g : 1-cell-Globular-Type x y}
    {H K : 2-cell-Globular-Type f g} (α β : 3-cell-Globular-Type H K) → UU l2
  4-cell-Globular-Type =
    4-cell-globular-structure globular-structure-0-cell-Globular-Type
```

## Examples

### The globular structure on a type given by its identity types

```agda
globular-structure-Id : {l : Level} (A : UU l) → globular-structure l A
globular-structure-Id A =
  λ where
  .1-cell-globular-structure x y →
    x ＝ y
  .globular-structure-1-cell-globular-structure x y →
    globular-structure-Id (x ＝ y)
```
