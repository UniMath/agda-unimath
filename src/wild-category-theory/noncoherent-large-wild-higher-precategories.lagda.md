# Noncoherent large wild higher precategories

```agda
{-# OPTIONS --guardedness #-}

module wild-category-theory.noncoherent-large-wild-higher-precategories where
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

open import structured-types.globular-types
open import structured-types.large-globular-types
open import structured-types.large-reflexive-globular-types
open import structured-types.large-transitive-globular-types
open import structured-types.reflexive-globular-types
open import structured-types.transitive-globular-types

open import wild-category-theory.noncoherent-wild-higher-precategories
```

</details>

## Idea

It is an important open problem known as the _coherence problem_ to define a
fully coherent notion of $∞$-category in univalent type theory. The subject of
_wild category theory_ attempts to recover some of the benefits of $∞$-category
theory without tackling this problem. We introduce, as one of our basic building
blocks in this subject, the notion of a _large noncoherent wild higher
precategory_.

A _large noncoherent wild higher precategory_ `𝒞` is a structure that attempts
at capturing the structure of a large higher precategory to the $0$'th order. It
consists of in some sense all of the operations and none of the coherence of a
large higher precategory. Thus, it is defined as a
[large globular type](structured-types.large-globular-types.md) with families of
$n$-morphisms labeled as "identities"

```text
  id-hom : (x : 𝑛-Cell 𝒞) → (𝑛+1)-Cell 𝒞 x x
```

and a composition operation at every dimension

```text
  comp-hom :
    {x y z : 𝑛-Cell 𝒞} → (𝑛+1)-Cell 𝒞 y z → (𝑛+1)-Cell 𝒞 x y → (𝑛+1)-Cell 𝒞 x z.
```

Entirely concretely, we define a
{{#concept "noncoherent large wild higher precategory" Agda=Noncoherent-Large-Wild-Higher-Precategory}}
to be a [reflexive](structured-types.reflexive-globular-types.md) and
[transitive](structured-types.transitive-globular-types.md) large globular type.
We call the 0-cells the _objects_, the 1-cells the _morphisms_ and the higher
cells the _$n$-morphisms_. The reflexivities are called the _identity
morphisms_, and the transitivity operations are branded as _composition of
morphisms_.

## Definitions

### Noncoherent large wild higher precategories

```agda
record
  Noncoherent-Large-Wild-Higher-Precategory
  (α : Level → Level) (β : Level → Level → Level) : UUω
  where
```

- The underlying large globular type of a noncoherent large wild precategory

```agda
  field
    large-globular-type-Noncoherent-Large-Wild-Precategory :
      Large-Globular-Type α β
```

- The type of objects of a noncoherent large wild higher precategory

```agda
  obj-Noncoherent-Large-Wild-Higher-Precategory : (l : Level) → UU (α l)
  obj-Noncoherent-Large-Wild-Higher-Precategory =
    0-cell-Large-Globular-Type
      large-globular-type-Noncoherent-Large-Wild-Precategory
```

- The globular type of morphisms between two objects in a noncoherent large wild
  higher precategory

```agda
  hom-globular-type-Noncoherent-Large-Wild-Higher-Precategory :
    {l1 l2 : Level}
    (x : obj-Noncoherent-Large-Wild-Higher-Precategory l1)
    (y : obj-Noncoherent-Large-Wild-Higher-Precategory l2) →
    Globular-Type (β l1 l2) (β l1 l2)
  hom-globular-type-Noncoherent-Large-Wild-Higher-Precategory =
    1-cell-globular-type-Large-Globular-Type
      large-globular-type-Noncoherent-Large-Wild-Precategory

  hom-Noncoherent-Large-Wild-Higher-Precategory :
    {l1 l2 : Level}
    (x : obj-Noncoherent-Large-Wild-Higher-Precategory l1)
    (y : obj-Noncoherent-Large-Wild-Higher-Precategory l2) →
    UU (β l1 l2)
  hom-Noncoherent-Large-Wild-Higher-Precategory =
    1-cell-Large-Globular-Type
      large-globular-type-Noncoherent-Large-Wild-Precategory
```

- The globular structure on the type of objects of a noncoherent large wild
  higher precategory

```agda
  globular-structure-obj-Noncoherent-Large-Wild-Higher-Precategory :
    large-globular-structure β obj-Noncoherent-Large-Wild-Higher-Precategory
  globular-structure-obj-Noncoherent-Large-Wild-Higher-Precategory =
    large-globular-structure-0-cell-Large-Globular-Type
      large-globular-type-Noncoherent-Large-Wild-Precategory
```

- The globular type of 2-morphisms is a noncoherent large wild higher
  precategory

```agda
  2-hom-globular-type-Noncoherent-Large-Wild-Higher-Precategory :
    {l1 l2 : Level}
    {x : obj-Noncoherent-Large-Wild-Higher-Precategory l1}
    {y : obj-Noncoherent-Large-Wild-Higher-Precategory l2}
    (f g : hom-Noncoherent-Large-Wild-Higher-Precategory x y) →
    Globular-Type (β l1 l2) (β l1 l2)
  2-hom-globular-type-Noncoherent-Large-Wild-Higher-Precategory =
    2-cell-globular-type-Large-Globular-Type
      large-globular-type-Noncoherent-Large-Wild-Precategory

  2-hom-Noncoherent-Large-Wild-Higher-Precategory :
    {l1 l2 : Level}
    {x : obj-Noncoherent-Large-Wild-Higher-Precategory l1}
    {y : obj-Noncoherent-Large-Wild-Higher-Precategory l2} →
    (f g : hom-Noncoherent-Large-Wild-Higher-Precategory x y) → UU (β l1 l2)
  2-hom-Noncoherent-Large-Wild-Higher-Precategory =
    2-cell-Large-Globular-Type
      large-globular-type-Noncoherent-Large-Wild-Precategory
```

- The globular structure on the type of morphisms between two objects in a
  noncoherent large wild higher precategory

```agda
  globular-structure-hom-Noncoherent-Large-Wild-Higher-Precategory :
    {l1 l2 : Level}
    (x : obj-Noncoherent-Large-Wild-Higher-Precategory l1)
    (y : obj-Noncoherent-Large-Wild-Higher-Precategory l2) →
    globular-structure
      ( β l1 l2)
      ( hom-Noncoherent-Large-Wild-Higher-Precategory x y)
  globular-structure-hom-Noncoherent-Large-Wild-Higher-Precategory =
    globular-structure-1-cell-Large-Globular-Type
      large-globular-type-Noncoherent-Large-Wild-Precategory
```

- The globular type of 3-morphisms in a noncoherent large wild higher
  precategory

```agda
  3-hom-globular-type-Noncoherent-Large-Wild-Higher-Precategory :
    {l1 l2 : Level}
    {x : obj-Noncoherent-Large-Wild-Higher-Precategory l1}
    {y : obj-Noncoherent-Large-Wild-Higher-Precategory l2}
    {f g : hom-Noncoherent-Large-Wild-Higher-Precategory x y}
    (s t : 2-hom-Noncoherent-Large-Wild-Higher-Precategory f g) →
    Globular-Type (β l1 l2) (β l1 l2)
  3-hom-globular-type-Noncoherent-Large-Wild-Higher-Precategory =
    3-cell-globular-type-Large-Globular-Type
      large-globular-type-Noncoherent-Large-Wild-Precategory

  3-hom-Noncoherent-Large-Wild-Higher-Precategory :
    {l1 l2 : Level}
    {x : obj-Noncoherent-Large-Wild-Higher-Precategory l1}
    {y : obj-Noncoherent-Large-Wild-Higher-Precategory l2}
    {f g : hom-Noncoherent-Large-Wild-Higher-Precategory x y} →
    2-hom-Noncoherent-Large-Wild-Higher-Precategory f g →
    2-hom-Noncoherent-Large-Wild-Higher-Precategory f g →
    UU (β l1 l2)
  3-hom-Noncoherent-Large-Wild-Higher-Precategory =
    3-cell-large-globular-structure
      ( globular-structure-obj-Noncoherent-Large-Wild-Higher-Precategory)
```

- The globular structure on the type of 2-morphisms in a noncoherent large wild
  higher precategory

```agda
  globular-structure-2-hom-Noncoherent-Large-Wild-Higher-Precategory :
    {l1 l2 : Level}
    {x : obj-Noncoherent-Large-Wild-Higher-Precategory l1}
    {y : obj-Noncoherent-Large-Wild-Higher-Precategory l2}
    (f g : hom-Noncoherent-Large-Wild-Higher-Precategory x y) →
    globular-structure
      ( β l1 l2)
      ( 2-hom-Noncoherent-Large-Wild-Higher-Precategory f g)
  globular-structure-2-hom-Noncoherent-Large-Wild-Higher-Precategory =
    globular-structure-2-cell-Large-Globular-Type
      large-globular-type-Noncoherent-Large-Wild-Precategory
```

- The structure of identity morphisms in a noncoherent large wild higher
  precategory

```agda
  field
    id-structure-Noncoherent-Large-Wild-Higher-Precategory :
      is-reflexive-Large-Globular-Type
        large-globular-type-Noncoherent-Large-Wild-Precategory

  id-hom-Noncoherent-Large-Wild-Higher-Precategory :
    {l1 : Level} (x : obj-Noncoherent-Large-Wild-Higher-Precategory l1) →
    hom-Noncoherent-Large-Wild-Higher-Precategory x x
  id-hom-Noncoherent-Large-Wild-Higher-Precategory =
    refl-0-cell-is-reflexive-Large-Globular-Type
      id-structure-Noncoherent-Large-Wild-Higher-Precategory

  id-structure-hom-globular-type-Noncoherent-Large-Wild-Higher-Precategory :
    {l1 l2 : Level}
    {x : obj-Noncoherent-Large-Wild-Higher-Precategory l1}
    {y : obj-Noncoherent-Large-Wild-Higher-Precategory l2} →
    is-reflexive-Globular-Type
      ( hom-globular-type-Noncoherent-Large-Wild-Higher-Precategory x y)
  id-structure-hom-globular-type-Noncoherent-Large-Wild-Higher-Precategory =
    is-reflexive-1-cell-globular-type-is-reflexive-Large-Globular-Type
      id-structure-Noncoherent-Large-Wild-Higher-Precategory

  id-2-hom-Noncoherent-Large-Wild-Higher-Precategory :
    {l1 l2 : Level}
    {x : obj-Noncoherent-Large-Wild-Higher-Precategory l1}
    {y : obj-Noncoherent-Large-Wild-Higher-Precategory l2}
    (f : hom-Noncoherent-Large-Wild-Higher-Precategory x y) →
    2-hom-Noncoherent-Large-Wild-Higher-Precategory f f
  id-2-hom-Noncoherent-Large-Wild-Higher-Precategory =
    refl-1-cell-is-reflexive-Large-Globular-Type
      id-structure-Noncoherent-Large-Wild-Higher-Precategory

  id-3-hom-Noncoherent-Large-Wild-Higher-Precategory :
    {l1 l2 : Level}
    {x : obj-Noncoherent-Large-Wild-Higher-Precategory l1}
    {y : obj-Noncoherent-Large-Wild-Higher-Precategory l2}
    {f g : hom-Noncoherent-Large-Wild-Higher-Precategory x y}
    (s : 2-hom-Noncoherent-Large-Wild-Higher-Precategory f g) →
    3-hom-Noncoherent-Large-Wild-Higher-Precategory s s
  id-3-hom-Noncoherent-Large-Wild-Higher-Precategory =
    refl-2-cell-is-reflexive-Large-Globular-Type
      id-structure-Noncoherent-Large-Wild-Higher-Precategory
```

- The structure of composition in a noncoherent large wild higher precategory

```agda
  field
    comp-structure-Noncoherent-Large-Wild-Higher-Precategory :
      is-transitive-large-globular-structure
        globular-structure-obj-Noncoherent-Large-Wild-Higher-Precategory

  comp-hom-Noncoherent-Large-Wild-Higher-Precategory :
    {l1 l2 l3 : Level}
    {x : obj-Noncoherent-Large-Wild-Higher-Precategory l1}
    {y : obj-Noncoherent-Large-Wild-Higher-Precategory l2}
    {z : obj-Noncoherent-Large-Wild-Higher-Precategory l3} →
    hom-Noncoherent-Large-Wild-Higher-Precategory y z →
    hom-Noncoherent-Large-Wild-Higher-Precategory x y →
    hom-Noncoherent-Large-Wild-Higher-Precategory x z
  comp-hom-Noncoherent-Large-Wild-Higher-Precategory =
    comp-1-cell-is-transitive-large-globular-structure
      comp-structure-Noncoherent-Large-Wild-Higher-Precategory

  comp-structure-hom-globular-type-Noncoherent-Large-Wild-Higher-Precategory :
    {l1 l2 : Level}
    (x : obj-Noncoherent-Large-Wild-Higher-Precategory l1)
    (y : obj-Noncoherent-Large-Wild-Higher-Precategory l2) →
    is-transitive-globular-structure
      ( globular-structure-hom-Noncoherent-Large-Wild-Higher-Precategory x y)
  comp-structure-hom-globular-type-Noncoherent-Large-Wild-Higher-Precategory =
    is-transitive-globular-structure-1-cell-is-transitive-large-globular-structure
      comp-structure-Noncoherent-Large-Wild-Higher-Precategory

  comp-2-hom-Noncoherent-Large-Wild-Higher-Precategory :
    {l1 l2 : Level}
    {x : obj-Noncoherent-Large-Wild-Higher-Precategory l1}
    {y : obj-Noncoherent-Large-Wild-Higher-Precategory l2}
    {f g h : hom-Noncoherent-Large-Wild-Higher-Precategory x y} →
    2-hom-Noncoherent-Large-Wild-Higher-Precategory g h →
    2-hom-Noncoherent-Large-Wild-Higher-Precategory f g →
    2-hom-Noncoherent-Large-Wild-Higher-Precategory f h
  comp-2-hom-Noncoherent-Large-Wild-Higher-Precategory =
    comp-2-cell-is-transitive-large-globular-structure
      comp-structure-Noncoherent-Large-Wild-Higher-Precategory

  comp-3-hom-Noncoherent-Large-Wild-Higher-Precategory :
    {l1 l2 : Level}
    {x : obj-Noncoherent-Large-Wild-Higher-Precategory l1}
    {y : obj-Noncoherent-Large-Wild-Higher-Precategory l2}
    {f g : hom-Noncoherent-Large-Wild-Higher-Precategory x y}
    {r s t : 2-hom-Noncoherent-Large-Wild-Higher-Precategory f g} →
    3-hom-Noncoherent-Large-Wild-Higher-Precategory s t →
    3-hom-Noncoherent-Large-Wild-Higher-Precategory r s →
    3-hom-Noncoherent-Large-Wild-Higher-Precategory r t
  comp-3-hom-Noncoherent-Large-Wild-Higher-Precategory =
    comp-3-cell-is-transitive-large-globular-structure
      comp-structure-Noncoherent-Large-Wild-Higher-Precategory
```

- The noncoherent wild higher precategory of morphisms between two object in a
  noncoherent large wild higher precategory

```agda
  hom-noncoherent-wild-higher-precategory-Noncoherent-Large-Wild-Precategory :
    {l1 l2 : Level}
    (x : obj-Noncoherent-Large-Wild-Higher-Precategory l1)
    (y : obj-Noncoherent-Large-Wild-Higher-Precategory l2) →
    Noncoherent-Wild-Higher-Precategory (β l1 l2) (β l1 l2)
  hom-noncoherent-wild-higher-precategory-Noncoherent-Large-Wild-Precategory
    x y =
    make-Noncoherent-Wild-Higher-Precategory
      ( hom-Noncoherent-Large-Wild-Higher-Precategory x y)
      ( globular-structure-hom-Noncoherent-Large-Wild-Higher-Precategory x y)
      ( id-structure-hom-globular-type-Noncoherent-Large-Wild-Higher-Precategory)
      ( comp-structure-hom-globular-type-Noncoherent-Large-Wild-Higher-Precategory
        x y)

open Noncoherent-Large-Wild-Higher-Precategory public
```
