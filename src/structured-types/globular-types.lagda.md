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
       -------------
     /   //     \\   \
    /   //   α   \\   ∨
   x  H|| ≡≡≡≡≡≡> ||K  y.
    \   \\       //   ∧
     \   V       V   /
       -------------
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

#### Infrastructure for globular structures

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
record
  Globular-Type
    (l1 l2 : Level) : UU (lsuc l1 ⊔ lsuc l2)
  where
  coinductive
  field
    0-cell-Globular-Type : UU l1
    1-cell-globular-type-Globular-Type :
      (x y : 0-cell-Globular-Type) → Globular-Type l2 l2

open Globular-Type public

make-Globular-Type :
  {l1 l2 : Level} {A : UU l1} →
  globular-structure l2 A → Globular-Type l1 l2
0-cell-Globular-Type
  ( make-Globular-Type {A = A} B) = A
1-cell-globular-type-Globular-Type
  ( make-Globular-Type B)
  x y =
  make-Globular-Type
    ( globular-structure-1-cell-globular-structure B x y)

globular-type-1-cell-globular-structure :
  {l1 l2 : Level} {A : UU l1} (B : globular-structure l2 A) →
  (x y : A) → Globular-Type l2 l2
globular-type-1-cell-globular-structure B x y =
  make-Globular-Type
    ( globular-structure-1-cell-globular-structure B x y)

globular-type-2-cell-globular-structure :
  {l1 l2 : Level} {A : UU l1} (B : globular-structure l2 A) →
  {x y : A} (f g : 1-cell-globular-structure B x y) → Globular-Type l2 l2
globular-type-2-cell-globular-structure B f g =
  make-Globular-Type
    ( globular-structure-2-cell-globular-structure B f g)

1-cell-Globular-Type :
  {l1 l2 : Level} (A : Globular-Type l1 l2)
  (x y : 0-cell-Globular-Type A) → UU l2
1-cell-Globular-Type A x y =
  0-cell-Globular-Type (1-cell-globular-type-Globular-Type A x y)

2-cell-Globular-Type :
  {l1 l2 : Level} (A : Globular-Type l1 l2)
  {x y : 0-cell-Globular-Type A}
  (f g : 1-cell-Globular-Type A x y) → UU l2
2-cell-Globular-Type A =
  1-cell-Globular-Type (1-cell-globular-type-Globular-Type A _ _)

3-cell-Globular-Type :
  {l1 l2 : Level} (A : Globular-Type l1 l2)
  {x y : 0-cell-Globular-Type A}
  {f g : 1-cell-Globular-Type A x y}
  (s t : 2-cell-Globular-Type A f g) → UU l2
3-cell-Globular-Type A =
  2-cell-Globular-Type (1-cell-globular-type-Globular-Type A _ _)

4-cell-Globular-Type :
  {l1 l2 : Level} (A : Globular-Type l1 l2)
  {x y : 0-cell-Globular-Type A}
  {f g : 1-cell-Globular-Type A x y}
  {s t : 2-cell-Globular-Type A f g}
  (u v : 3-cell-Globular-Type A s t) → UU l2
4-cell-Globular-Type A =
  3-cell-Globular-Type (1-cell-globular-type-Globular-Type A _ _)

5-cell-Globular-Type :
  {l1 l2 : Level} (A : Globular-Type l1 l2)
  {x y : 0-cell-Globular-Type A}
  {f g : 1-cell-Globular-Type A x y}
  {s t : 2-cell-Globular-Type A f g}
  {u v : 3-cell-Globular-Type A s t}
  (α β : 4-cell-Globular-Type A u v) → UU l2
5-cell-Globular-Type A =
  4-cell-Globular-Type (1-cell-globular-type-Globular-Type A _ _)

2-cell-globular-type-Globular-Type :
  {l1 l2 : Level} (A : Globular-Type l1 l2)
  {x y : 0-cell-Globular-Type A}
  (f g : 1-cell-Globular-Type A x y) → Globular-Type l2 l2
2-cell-globular-type-Globular-Type A =
  1-cell-globular-type-Globular-Type (1-cell-globular-type-Globular-Type A _ _)

3-cell-globular-type-Globular-Type :
  {l1 l2 : Level} (A : Globular-Type l1 l2)
  {x y : 0-cell-Globular-Type A}
  {f g : 1-cell-Globular-Type A x y}
  (s t : 2-cell-Globular-Type A f g) → Globular-Type l2 l2
3-cell-globular-type-Globular-Type A =
  1-cell-globular-type-Globular-Type (2-cell-globular-type-Globular-Type A _ _)

4-cell-globular-type-Globular-Type :
  {l1 l2 : Level} (A : Globular-Type l1 l2)
  {x y : 0-cell-Globular-Type A}
  {f g : 1-cell-Globular-Type A x y}
  {s t : 2-cell-Globular-Type A f g}
  (u v : 3-cell-Globular-Type A s t) → Globular-Type l2 l2
4-cell-globular-type-Globular-Type A =
  1-cell-globular-type-Globular-Type (3-cell-globular-type-Globular-Type A _ _)

5-cell-globular-type-Globular-Type :
  {l1 l2 : Level} (A : Globular-Type l1 l2)
  {x y : 0-cell-Globular-Type A}
  {f g : 1-cell-Globular-Type A x y}
  {s t : 2-cell-Globular-Type A f g}
  {u v : 3-cell-Globular-Type A s t}
  (α β : 4-cell-Globular-Type A u v) → Globular-Type l2 l2
5-cell-globular-type-Globular-Type A =
  1-cell-globular-type-Globular-Type (4-cell-globular-type-Globular-Type A _ _)

globular-structure-0-cell-Globular-Type :
  {l1 l2 : Level} (A : Globular-Type l1 l2) →
  globular-structure l2 (0-cell-Globular-Type A)
1-cell-globular-structure
  ( globular-structure-0-cell-Globular-Type A) =
  1-cell-Globular-Type A
globular-structure-1-cell-globular-structure
  ( globular-structure-0-cell-Globular-Type A) x y =
  globular-structure-0-cell-Globular-Type
    ( 1-cell-globular-type-Globular-Type A x y)

globular-structure-1-cell-Globular-Type :
  {l1 l2 : Level} (A : Globular-Type l1 l2) (x y : 0-cell-Globular-Type A) →
  globular-structure l2 (1-cell-Globular-Type A x y)
globular-structure-1-cell-Globular-Type A x y =
  globular-structure-0-cell-Globular-Type
    ( 1-cell-globular-type-Globular-Type A x y)

globular-structure-2-cell-Globular-Type :
  {l1 l2 : Level} (A : Globular-Type l1 l2)
  {x y : 0-cell-Globular-Type A}
  (f g : 1-cell-Globular-Type A x y) →
  globular-structure l2 (2-cell-Globular-Type A f g)
globular-structure-2-cell-Globular-Type A =
  globular-structure-1-cell-Globular-Type
    ( 1-cell-globular-type-Globular-Type A _ _)

globular-structure-3-cell-Globular-Type :
  {l1 l2 : Level} (A : Globular-Type l1 l2)
  {x y : 0-cell-Globular-Type A}
  {f g : 1-cell-Globular-Type A x y}
  (s t : 2-cell-Globular-Type A f g) →
  globular-structure l2 (3-cell-Globular-Type A s t)
globular-structure-3-cell-Globular-Type A =
  globular-structure-2-cell-Globular-Type
    ( 1-cell-globular-type-Globular-Type A _ _)

globular-structure-4-cell-Globular-Type :
  {l1 l2 : Level} (A : Globular-Type l1 l2)
  {x y : 0-cell-Globular-Type A}
  {f g : 1-cell-Globular-Type A x y}
  {s t : 2-cell-Globular-Type A f g}
  (u v : 3-cell-Globular-Type A s t) →
  globular-structure l2 (4-cell-Globular-Type A u v)
globular-structure-4-cell-Globular-Type A =
  globular-structure-3-cell-Globular-Type
    ( 1-cell-globular-type-Globular-Type A _ _)

globular-structure-5-cell-Globular-Type :
  {l1 l2 : Level} (A : Globular-Type l1 l2)
  {x y : 0-cell-Globular-Type A}
  {f g : 1-cell-Globular-Type A x y}
  {s t : 2-cell-Globular-Type A f g}
  {u v : 3-cell-Globular-Type A s t}
  (α β : 4-cell-Globular-Type A u v) →
  globular-structure l2 (5-cell-Globular-Type A α β)
globular-structure-5-cell-Globular-Type A =
  globular-structure-4-cell-Globular-Type
    ( 1-cell-globular-type-Globular-Type A _ _)
```

## Examples

### The globular structure on a type given by its identity types

```agda
globular-type-Type : {l : Level} → UU l → Globular-Type l l
0-cell-Globular-Type (globular-type-Type A) = A
1-cell-globular-type-Globular-Type (globular-type-Type A) x y =
  globular-type-Type (x ＝ y)

globular-structure-Id : {l : Level} (A : UU l) → globular-structure l A
1-cell-globular-structure (globular-structure-Id A) x y = x ＝ y
globular-structure-1-cell-globular-structure (globular-structure-Id A) x y =
  globular-structure-Id (x ＝ y)
```

## See also

- [Reflexive globular types](structured-types.reflexive-globular-types.md)
- [Symmetric globular types](structured-types.symmetric-globular-types.md)
- [Transitive globular types](structured-types.transitive-globular-types.md)
