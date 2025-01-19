# Noncoherent large ω-precategories

```agda
{-# OPTIONS --guardedness #-}

module wild-category-theory.noncoherent-large-omega-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.precategories

open import foundation.action-on-identifications-binary-functions
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.sets
open import foundation.strictly-involutive-identity-types
open import foundation.universe-levels

open import globular-types.globular-types
open import globular-types.large-globular-types
open import globular-types.large-reflexive-globular-types
open import globular-types.large-transitive-globular-types
open import globular-types.reflexive-globular-types
open import globular-types.transitive-globular-types

open import wild-category-theory.noncoherent-omega-precategories
```

</details>

## Idea

It is an important open problem known as the _coherence problem_ to define a
fully coherent notion of $∞$-category or higher variants in univalent type
theory. The subject of _wild category theory_ attempts to recover some of the
benefits of $∞$-category theory without tackling this problem. We introduce, as
one of our basic building blocks in this subject, the notion of a _noncoherent
large ω-precategory_.

A _noncoherent large ω-precategory_ `𝒞` is a structure that attempts at
capturing the structure of a large ω-category to the $0$'th order. It consists
of in some sense all of the operations and none of the coherence. Thus, it is
defined as a [large globular type](globular-types.large-globular-types.md) with
families of $n$-morphisms labeled as "identities"

```text
  id-hom : (x : 𝒞ₙ) → 𝒞ₙ₊₁ x x
```

and a composition operation at every dimension

```text
  comp-hom : {x y z : 𝒞ₙ} → 𝒞ₙ₊₁ y z → 𝒞ₙ₊₁ x y → 𝒞ₙ₊₁ x z.
```

Entirely concretely, we define a
{{#concept "noncoherent large ω-precategory" Agda=Noncoherent-Large-ω-Precategory}}
to be a [reflexive](globular-types.reflexive-globular-types.md) and
[transitive](globular-types.transitive-globular-types.md) large globular type.
We call the 0-cells the _objects_, the 1-cells the _morphisms_ and the higher
cells the _$n$-morphisms_. The reflexivities are called the _identity
morphisms_, and the transitivity operations are branded as _composition of
morphisms_.

## Definitions

### Noncoherent large ω-precategories

```agda
record
  Noncoherent-Large-ω-Precategory
  (α : Level → Level) (β : Level → Level → Level) : UUω
  where
```

The underlying large globular type of a noncoherent large wild precategory:

```agda
  field
    large-globular-type-Noncoherent-Large-ω-Precategory :
      Large-Globular-Type α β
```

The type of objects of a noncoherent large ω-precategory:

```agda
  obj-Noncoherent-Large-ω-Precategory : (l : Level) → UU (α l)
  obj-Noncoherent-Large-ω-Precategory =
    0-cell-Large-Globular-Type
      large-globular-type-Noncoherent-Large-ω-Precategory
```

The globular type of morphisms between two objects in a noncoherent large
ω-precategory:

```agda
  hom-globular-type-Noncoherent-Large-ω-Precategory :
    {l1 l2 : Level}
    (x : obj-Noncoherent-Large-ω-Precategory l1)
    (y : obj-Noncoherent-Large-ω-Precategory l2) →
    Globular-Type (β l1 l2) (β l1 l2)
  hom-globular-type-Noncoherent-Large-ω-Precategory =
    1-cell-globular-type-Large-Globular-Type
      large-globular-type-Noncoherent-Large-ω-Precategory

  hom-Noncoherent-Large-ω-Precategory :
    {l1 l2 : Level}
    (x : obj-Noncoherent-Large-ω-Precategory l1)
    (y : obj-Noncoherent-Large-ω-Precategory l2) →
    UU (β l1 l2)
  hom-Noncoherent-Large-ω-Precategory =
    1-cell-Large-Globular-Type
      large-globular-type-Noncoherent-Large-ω-Precategory
```

The globular structure on the type of objects of a noncoherent large
ω-precategory:

```agda
  globular-structure-obj-Noncoherent-Large-ω-Precategory :
    large-globular-structure β obj-Noncoherent-Large-ω-Precategory
  globular-structure-obj-Noncoherent-Large-ω-Precategory =
    large-globular-structure-0-cell-Large-Globular-Type
      large-globular-type-Noncoherent-Large-ω-Precategory
```

The globular type of 2-morphisms is a noncoherent large ω-precategory:

```agda
  2-hom-globular-type-Noncoherent-Large-ω-Precategory :
    {l1 l2 : Level}
    {x : obj-Noncoherent-Large-ω-Precategory l1}
    {y : obj-Noncoherent-Large-ω-Precategory l2}
    (f g : hom-Noncoherent-Large-ω-Precategory x y) →
    Globular-Type (β l1 l2) (β l1 l2)
  2-hom-globular-type-Noncoherent-Large-ω-Precategory =
    2-cell-globular-type-Large-Globular-Type
      large-globular-type-Noncoherent-Large-ω-Precategory

  2-hom-Noncoherent-Large-ω-Precategory :
    {l1 l2 : Level}
    {x : obj-Noncoherent-Large-ω-Precategory l1}
    {y : obj-Noncoherent-Large-ω-Precategory l2} →
    (f g : hom-Noncoherent-Large-ω-Precategory x y) → UU (β l1 l2)
  2-hom-Noncoherent-Large-ω-Precategory =
    2-cell-Large-Globular-Type
      large-globular-type-Noncoherent-Large-ω-Precategory
```

The globular structure on the type of morphisms between two objects in a
noncoherent large ω-precategory:

```agda
  globular-structure-hom-Noncoherent-Large-ω-Precategory :
    {l1 l2 : Level}
    (x : obj-Noncoherent-Large-ω-Precategory l1)
    (y : obj-Noncoherent-Large-ω-Precategory l2) →
    globular-structure
      ( β l1 l2)
      ( hom-Noncoherent-Large-ω-Precategory x y)
  globular-structure-hom-Noncoherent-Large-ω-Precategory =
    globular-structure-1-cell-Large-Globular-Type
      large-globular-type-Noncoherent-Large-ω-Precategory
```

The globular type of 3-morphisms in a noncoherent large ω-precategory:

```agda
  3-hom-globular-type-Noncoherent-Large-ω-Precategory :
    {l1 l2 : Level}
    {x : obj-Noncoherent-Large-ω-Precategory l1}
    {y : obj-Noncoherent-Large-ω-Precategory l2}
    {f g : hom-Noncoherent-Large-ω-Precategory x y}
    (s t : 2-hom-Noncoherent-Large-ω-Precategory f g) →
    Globular-Type (β l1 l2) (β l1 l2)
  3-hom-globular-type-Noncoherent-Large-ω-Precategory =
    3-cell-globular-type-Large-Globular-Type
      large-globular-type-Noncoherent-Large-ω-Precategory

  3-hom-Noncoherent-Large-ω-Precategory :
    {l1 l2 : Level}
    {x : obj-Noncoherent-Large-ω-Precategory l1}
    {y : obj-Noncoherent-Large-ω-Precategory l2}
    {f g : hom-Noncoherent-Large-ω-Precategory x y} →
    2-hom-Noncoherent-Large-ω-Precategory f g →
    2-hom-Noncoherent-Large-ω-Precategory f g →
    UU (β l1 l2)
  3-hom-Noncoherent-Large-ω-Precategory =
    3-cell-Large-Globular-Type
      large-globular-type-Noncoherent-Large-ω-Precategory
```

The globular structure on the type of 2-morphisms in a noncoherent large
ω-precategory:

```agda
  globular-structure-2-hom-Noncoherent-Large-ω-Precategory :
    {l1 l2 : Level}
    {x : obj-Noncoherent-Large-ω-Precategory l1}
    {y : obj-Noncoherent-Large-ω-Precategory l2}
    (f g : hom-Noncoherent-Large-ω-Precategory x y) →
    globular-structure
      ( β l1 l2)
      ( 2-hom-Noncoherent-Large-ω-Precategory f g)
  globular-structure-2-hom-Noncoherent-Large-ω-Precategory =
    globular-structure-2-cell-Large-Globular-Type
      large-globular-type-Noncoherent-Large-ω-Precategory
```

The structure of identity morphisms in a noncoherent large ω-precategory:

```agda
  field
    id-structure-Noncoherent-Large-ω-Precategory :
      is-reflexive-Large-Globular-Type
        large-globular-type-Noncoherent-Large-ω-Precategory

  id-hom-Noncoherent-Large-ω-Precategory :
    {l1 : Level} {x : obj-Noncoherent-Large-ω-Precategory l1} →
    hom-Noncoherent-Large-ω-Precategory x x
  id-hom-Noncoherent-Large-ω-Precategory {l1} {x} =
    refl-1-cell-is-reflexive-Large-Globular-Type
      ( id-structure-Noncoherent-Large-ω-Precategory)
      ( x)

  id-structure-hom-globular-type-Noncoherent-Large-ω-Precategory :
    {l1 l2 : Level}
    {x : obj-Noncoherent-Large-ω-Precategory l1}
    {y : obj-Noncoherent-Large-ω-Precategory l2} →
    is-reflexive-Globular-Type
      ( hom-globular-type-Noncoherent-Large-ω-Precategory x y)
  id-structure-hom-globular-type-Noncoherent-Large-ω-Precategory =
    is-reflexive-1-cell-globular-type-is-reflexive-Large-Globular-Type
      id-structure-Noncoherent-Large-ω-Precategory

  id-2-hom-Noncoherent-Large-ω-Precategory :
    {l1 l2 : Level}
    {x : obj-Noncoherent-Large-ω-Precategory l1}
    {y : obj-Noncoherent-Large-ω-Precategory l2}
    (f : hom-Noncoherent-Large-ω-Precategory x y) →
    2-hom-Noncoherent-Large-ω-Precategory f f
  id-2-hom-Noncoherent-Large-ω-Precategory =
    refl-2-cell-is-reflexive-Large-Globular-Type
      id-structure-Noncoherent-Large-ω-Precategory

  id-3-hom-Noncoherent-Large-ω-Precategory :
    {l1 l2 : Level}
    {x : obj-Noncoherent-Large-ω-Precategory l1}
    {y : obj-Noncoherent-Large-ω-Precategory l2}
    {f g : hom-Noncoherent-Large-ω-Precategory x y}
    (s : 2-hom-Noncoherent-Large-ω-Precategory f g) →
    3-hom-Noncoherent-Large-ω-Precategory s s
  id-3-hom-Noncoherent-Large-ω-Precategory =
    refl-3-cell-is-reflexive-Large-Globular-Type
      id-structure-Noncoherent-Large-ω-Precategory
```

The structure of composition in a noncoherent large ω-precategory:

```agda
  field
    comp-structure-Noncoherent-Large-ω-Precategory :
      is-transitive-Large-Globular-Type
        large-globular-type-Noncoherent-Large-ω-Precategory

  comp-hom-Noncoherent-Large-ω-Precategory :
    {l1 l2 l3 : Level}
    {x : obj-Noncoherent-Large-ω-Precategory l1}
    {y : obj-Noncoherent-Large-ω-Precategory l2}
    {z : obj-Noncoherent-Large-ω-Precategory l3} →
    hom-Noncoherent-Large-ω-Precategory y z →
    hom-Noncoherent-Large-ω-Precategory x y →
    hom-Noncoherent-Large-ω-Precategory x z
  comp-hom-Noncoherent-Large-ω-Precategory =
    comp-1-cell-is-transitive-Large-Globular-Type
      comp-structure-Noncoherent-Large-ω-Precategory

  comp-structure-hom-globular-type-Noncoherent-Large-ω-Precategory :
    {l1 l2 : Level}
    {x : obj-Noncoherent-Large-ω-Precategory l1}
    {y : obj-Noncoherent-Large-ω-Precategory l2} →
    is-transitive-Globular-Type
      ( hom-globular-type-Noncoherent-Large-ω-Precategory x y)
  comp-structure-hom-globular-type-Noncoherent-Large-ω-Precategory =
    is-transitive-1-cell-globular-type-is-transitive-Large-Globular-Type
      comp-structure-Noncoherent-Large-ω-Precategory

  comp-2-hom-Noncoherent-Large-ω-Precategory :
    {l1 l2 : Level}
    {x : obj-Noncoherent-Large-ω-Precategory l1}
    {y : obj-Noncoherent-Large-ω-Precategory l2}
    {f g h : hom-Noncoherent-Large-ω-Precategory x y} →
    2-hom-Noncoherent-Large-ω-Precategory g h →
    2-hom-Noncoherent-Large-ω-Precategory f g →
    2-hom-Noncoherent-Large-ω-Precategory f h
  comp-2-hom-Noncoherent-Large-ω-Precategory =
    comp-2-cell-is-transitive-Large-Globular-Type
      comp-structure-Noncoherent-Large-ω-Precategory

  comp-3-hom-Noncoherent-Large-ω-Precategory :
    {l1 l2 : Level}
    {x : obj-Noncoherent-Large-ω-Precategory l1}
    {y : obj-Noncoherent-Large-ω-Precategory l2}
    {f g : hom-Noncoherent-Large-ω-Precategory x y}
    {r s t : 2-hom-Noncoherent-Large-ω-Precategory f g} →
    3-hom-Noncoherent-Large-ω-Precategory s t →
    3-hom-Noncoherent-Large-ω-Precategory r s →
    3-hom-Noncoherent-Large-ω-Precategory r t
  comp-3-hom-Noncoherent-Large-ω-Precategory =
    comp-3-cell-is-transitive-Large-Globular-Type
      comp-structure-Noncoherent-Large-ω-Precategory
```

The noncoherent ω-precategory of morphisms between two object in a noncoherent
large ω-precategory:

```agda
  hom-noncoherent-ω-precategory-Noncoherent-Large-ω-Precategory :
    {l1 l2 : Level}
    (x : obj-Noncoherent-Large-ω-Precategory l1)
    (y : obj-Noncoherent-Large-ω-Precategory l2) →
    Noncoherent-ω-Precategory (β l1 l2) (β l1 l2)
  hom-noncoherent-ω-precategory-Noncoherent-Large-ω-Precategory
    x y =
      make-Noncoherent-ω-Precategory
        ( id-structure-hom-globular-type-Noncoherent-Large-ω-Precategory
          { x = x}
          { y})
        ( comp-structure-hom-globular-type-Noncoherent-Large-ω-Precategory)
```

The underlying reflexive globular type of a noncoherent large ω-precategory:

```agda
  large-reflexive-globular-type-Noncoherent-Large-ω-Precategory :
    Large-Reflexive-Globular-Type α β
  large-globular-type-Large-Reflexive-Globular-Type
    large-reflexive-globular-type-Noncoherent-Large-ω-Precategory =
    large-globular-type-Noncoherent-Large-ω-Precategory
  is-reflexive-Large-Reflexive-Globular-Type
    large-reflexive-globular-type-Noncoherent-Large-ω-Precategory =
    id-structure-Noncoherent-Large-ω-Precategory
```

The underlying transitive globular type of a noncoherent large ω-precategory:

```agda
  large-transitive-globular-type-Noncoherent-Large-ω-Precategory :
    Large-Transitive-Globular-Type α β
  large-globular-type-Large-Transitive-Globular-Type
    large-transitive-globular-type-Noncoherent-Large-ω-Precategory =
    large-globular-type-Noncoherent-Large-ω-Precategory
  is-transitive-Large-Transitive-Globular-Type
    large-transitive-globular-type-Noncoherent-Large-ω-Precategory =
    comp-structure-Noncoherent-Large-ω-Precategory

open Noncoherent-Large-ω-Precategory public
```
