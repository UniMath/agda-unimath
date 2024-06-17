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

open import wild-category-theory.noncoherent-wild-higher-precategories
```

</details>

## Idea

It is a important open problem known as the _coherence problem_ to define a
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

  field
    obj-Noncoherent-Large-Wild-Higher-Precategory : (l : Level) → UU (α l)

    hom-globular-structure-Noncoherent-Large-Wild-Higher-Precategory :
      large-globular-structure β obj-Noncoherent-Large-Wild-Higher-Precategory

    id-hom-globular-structure-Noncoherent-Large-Wild-Higher-Precategory :
      is-reflexive-large-globular-structure
        ( hom-globular-structure-Noncoherent-Large-Wild-Higher-Precategory)

    comp-hom-globular-structure-Noncoherent-Large-Wild-Higher-Precategory :
      is-transitive-large-globular-structure
        ( hom-globular-structure-Noncoherent-Large-Wild-Higher-Precategory)

  large-globular-type-Noncoherent-Large-Wild-Higher-Precategory :
    Large-Globular-Type α β
  large-globular-type-Noncoherent-Large-Wild-Higher-Precategory =
    λ where
    .0-cell-Large-Globular-Type →
      obj-Noncoherent-Large-Wild-Higher-Precategory
    .globular-structure-0-cell-Large-Globular-Type →
      hom-globular-structure-Noncoherent-Large-Wild-Higher-Precategory
```

We record some common projections for noncoherent large wild higher
precategories.

```agda
  hom-Noncoherent-Large-Wild-Higher-Precategory :
    {l1 l2 : Level} →
    obj-Noncoherent-Large-Wild-Higher-Precategory l1 →
    obj-Noncoherent-Large-Wild-Higher-Precategory l2 →
    UU (β l1 l2)
  hom-Noncoherent-Large-Wild-Higher-Precategory =
    1-cell-large-globular-structure
      ( hom-globular-structure-Noncoherent-Large-Wild-Higher-Precategory)

  id-hom-Noncoherent-Large-Wild-Higher-Precategory :
    {l : Level} {x : obj-Noncoherent-Large-Wild-Higher-Precategory l} →
    hom-Noncoherent-Large-Wild-Higher-Precategory x x
  id-hom-Noncoherent-Large-Wild-Higher-Precategory =
    refl-1-cell-is-reflexive-large-globular-structure
      ( id-hom-globular-structure-Noncoherent-Large-Wild-Higher-Precategory)

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
      ( comp-hom-globular-structure-Noncoherent-Large-Wild-Higher-Precategory)

  hom-globular-type-Noncoherent-Large-Wild-Higher-Precategory :
    {l1 l2 : Level}
    (x : obj-Noncoherent-Large-Wild-Higher-Precategory l1)
    (y : obj-Noncoherent-Large-Wild-Higher-Precategory l2) →
    Globular-Type (β l1 l2) (β l1 l2)
  pr1 (hom-globular-type-Noncoherent-Large-Wild-Higher-Precategory x y) =
    hom-Noncoherent-Large-Wild-Higher-Precategory x y
  pr2 (hom-globular-type-Noncoherent-Large-Wild-Higher-Precategory x y) =
    globular-structure-1-cell-large-globular-structure
      ( hom-globular-structure-Noncoherent-Large-Wild-Higher-Precategory)
      ( x)
      ( y)

  hom-noncoherent-wild-higher-precategory-Noncoherent-Large-Wild-Higher-Precategory :
    {l1 l2 : Level}
    (x : obj-Noncoherent-Large-Wild-Higher-Precategory l1)
    (y : obj-Noncoherent-Large-Wild-Higher-Precategory l2) →
    Noncoherent-Wild-Higher-Precategory (β l1 l2) (β l1 l2)
  hom-noncoherent-wild-higher-precategory-Noncoherent-Large-Wild-Higher-Precategory
    x y =
    make-Noncoherent-Wild-Higher-Precategory
      ( hom-Noncoherent-Large-Wild-Higher-Precategory x y)
      ( globular-structure-1-cell-large-globular-structure
        ( hom-globular-structure-Noncoherent-Large-Wild-Higher-Precategory)
        ( x)
        ( y))
      ( is-reflexive-globular-structure-1-cell-is-reflexive-large-globular-structure
        ( id-hom-globular-structure-Noncoherent-Large-Wild-Higher-Precategory)
        ( x)
        ( y))
      ( is-transitive-globular-structure-1-cell-is-transitive-large-globular-structure
        ( comp-hom-globular-structure-Noncoherent-Large-Wild-Higher-Precategory)
        ( x)
        ( y))
```

```agda
  2-hom-Noncoherent-Large-Wild-Higher-Precategory :
    {l1 l2 : Level}
    {x : obj-Noncoherent-Large-Wild-Higher-Precategory l1}
    {y : obj-Noncoherent-Large-Wild-Higher-Precategory l2} →
    hom-Noncoherent-Large-Wild-Higher-Precategory x y →
    hom-Noncoherent-Large-Wild-Higher-Precategory x y →
    UU (β l1 l2)
  2-hom-Noncoherent-Large-Wild-Higher-Precategory =
    2-cell-large-globular-structure
      ( hom-globular-structure-Noncoherent-Large-Wild-Higher-Precategory)

  id-2-hom-Noncoherent-Large-Wild-Higher-Precategory :
    {l1 l2 : Level}
    {x : obj-Noncoherent-Large-Wild-Higher-Precategory l1}
    {y : obj-Noncoherent-Large-Wild-Higher-Precategory l2}
    {f : hom-Noncoherent-Large-Wild-Higher-Precategory x y} →
    2-hom-Noncoherent-Large-Wild-Higher-Precategory f f
  id-2-hom-Noncoherent-Large-Wild-Higher-Precategory =
    refl-2-cell-is-reflexive-large-globular-structure
      ( id-hom-globular-structure-Noncoherent-Large-Wild-Higher-Precategory)

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
      ( comp-hom-globular-structure-Noncoherent-Large-Wild-Higher-Precategory)
```

```agda
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
      ( hom-globular-structure-Noncoherent-Large-Wild-Higher-Precategory)

  id-3-hom-Noncoherent-Large-Wild-Higher-Precategory :
    {l1 l2 : Level}
    {x : obj-Noncoherent-Large-Wild-Higher-Precategory l1}
    {y : obj-Noncoherent-Large-Wild-Higher-Precategory l2}
    {f g : hom-Noncoherent-Large-Wild-Higher-Precategory x y}
    {H : 2-hom-Noncoherent-Large-Wild-Higher-Precategory f g} →
    3-hom-Noncoherent-Large-Wild-Higher-Precategory H H
  id-3-hom-Noncoherent-Large-Wild-Higher-Precategory =
    refl-3-cell-is-reflexive-large-globular-structure
      ( id-hom-globular-structure-Noncoherent-Large-Wild-Higher-Precategory)

  comp-3-hom-Noncoherent-Large-Wild-Higher-Precategory :
    {l1 l2 : Level}
    {x : obj-Noncoherent-Large-Wild-Higher-Precategory l1}
    {y : obj-Noncoherent-Large-Wild-Higher-Precategory l2}
    {f g : hom-Noncoherent-Large-Wild-Higher-Precategory x y}
    {H K L : 2-hom-Noncoherent-Large-Wild-Higher-Precategory f g} →
    3-hom-Noncoherent-Large-Wild-Higher-Precategory K L →
    3-hom-Noncoherent-Large-Wild-Higher-Precategory H K →
    3-hom-Noncoherent-Large-Wild-Higher-Precategory H L
  comp-3-hom-Noncoherent-Large-Wild-Higher-Precategory =
    comp-3-cell-is-transitive-large-globular-structure
      ( comp-hom-globular-structure-Noncoherent-Large-Wild-Higher-Precategory)
```

```agda
open Noncoherent-Large-Wild-Higher-Precategory public
```
