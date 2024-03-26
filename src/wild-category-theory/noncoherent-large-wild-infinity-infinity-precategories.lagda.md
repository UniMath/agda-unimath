# Noncoherent large wild (∞,∞)-precategories

```agda
{-# OPTIONS --guardedness #-}

module wild-category-theory.noncoherent-large-wild-infinity-infinity-precategories where
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

open import wild-category-theory.noncoherent-wild-infinity-infinity-precategories
```

</details>

## Idea

A
{{#concept "noncoherent large wild $(∞,∞)$-precategory" Agda=Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory}}
is a [reflexive](structured-types.large-reflexive-globular-types.md) and
[transitive](structured-types.large-transitive-globular-types.md)
[large globular type](structured-types.large-globular-types.md). We call the
0-cells the _objects_, the 1-cells the _morphisms_ and the higher cells the
_$n$-morphisms_. The reflexivities are called the _identity morphisms_, and the
transitivity operations are branded as _composition of morphisms_.

## Definitions

### Noncoherent large wild $(∞,∞)$-precategories

```agda
record
  Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory
  (α : Level → Level) (β : Level → Level → Level) : UUω
  where

  field
    obj-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory : (l : Level) → UU (α l)

    hom-globular-structure-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory :
      large-globular-structure β obj-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory

    id-hom-globular-structure-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory :
      is-reflexive-large-globular-structure
        ( hom-globular-structure-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory)

    comp-hom-globular-structure-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory :
      is-transitive-large-globular-structure
        ( hom-globular-structure-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory)

  large-globular-type-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory :
    Large-Globular-Type α β
  large-globular-type-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory =
    λ where
    .0-cell-Large-Globular-Type →
      obj-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory
    .globular-structure-0-cell-Large-Globular-Type →
      hom-globular-structure-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory
```

We record some common projections for noncoherent large wild
$(∞,∞)$-precategories.

```agda
  hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory :
    {l1 l2 : Level} →
    obj-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory l1 →
    obj-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory l2 →
    UU (β l1 l2)
  hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory =
    1-cell-large-globular-structure
      ( hom-globular-structure-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory)

  id-hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory :
    {l : Level} {x : obj-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory l} →
    hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory x x
  id-hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory =
    refl-1-cell-is-reflexive-large-globular-structure
      ( id-hom-globular-structure-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory)

  comp-hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory :
    {l1 l2 l3 : Level}
    {x : obj-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory l1}
    {y : obj-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory l2}
    {z : obj-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory l3} →
    hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory y z →
    hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory x y →
    hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory x z
  comp-hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory =
    comp-1-cell-is-transitive-large-globular-structure
      ( comp-hom-globular-structure-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory)

  hom-globular-type-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory :
    {l1 l2 : Level}
    (x : obj-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory l1)
    (y : obj-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory l2) →
    Globular-Type (β l1 l2) (β l1 l2)
  pr1 (hom-globular-type-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory x y) =
    hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory x y
  pr2 (hom-globular-type-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory x y) =
    globular-structure-1-cell-large-globular-structure
      ( hom-globular-structure-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory)
      ( x)
      ( y)

  hom-noncoherent-wild-⟨∞,∞⟩-precategory-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory :
    {l1 l2 : Level}
    (x : obj-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory l1)
    (y : obj-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory l2) →
    Noncoherent-Wild-⟨∞,∞⟩-Precategory (β l1 l2) (β l1 l2)
  hom-noncoherent-wild-⟨∞,∞⟩-precategory-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory
    x y =
    make-Noncoherent-Wild-⟨∞,∞⟩-Precategory
      ( hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory x y)
      ( globular-structure-1-cell-large-globular-structure
        ( hom-globular-structure-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory)
        ( x)
        ( y))
      ( is-reflexive-globular-structure-1-cell-is-reflexive-large-globular-structure
        ( id-hom-globular-structure-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory)
        ( x)
        ( y))
      ( is-transitive-globular-structure-1-cell-is-transitive-large-globular-structure
        ( comp-hom-globular-structure-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory)
        ( x)
        ( y))
```

```agda
  2-hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory :
    {l1 l2 : Level}
    {x : obj-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory l1}
    {y : obj-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory l2} →
    hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory x y →
    hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory x y →
    UU (β l1 l2)
  2-hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory =
    2-cell-large-globular-structure
      ( hom-globular-structure-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory)

  id-2-hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory :
    {l1 l2 : Level}
    {x : obj-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory l1}
    {y : obj-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory l2}
    {f : hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory x y} →
    2-hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory f f
  id-2-hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory =
    refl-2-cell-is-reflexive-large-globular-structure
      ( id-hom-globular-structure-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory)

  comp-2-hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory :
    {l1 l2 : Level}
    {x : obj-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory l1}
    {y : obj-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory l2}
    {f g h : hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory x y} →
    2-hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory g h →
    2-hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory f g →
    2-hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory f h
  comp-2-hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory =
    comp-2-cell-is-transitive-large-globular-structure
      ( comp-hom-globular-structure-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory)
```

```agda
  3-hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory :
    {l1 l2 : Level}
    {x : obj-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory l1}
    {y : obj-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory l2}
    {f g : hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory x y} →
    2-hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory f g →
    2-hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory f g →
    UU (β l1 l2)
  3-hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory =
    3-cell-large-globular-structure
      ( hom-globular-structure-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory)

  id-3-hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory :
    {l1 l2 : Level}
    {x : obj-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory l1}
    {y : obj-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory l2}
    {f g : hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory x y}
    {H : 2-hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory f g} →
    3-hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory H H
  id-3-hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory =
    refl-3-cell-is-reflexive-large-globular-structure
      ( id-hom-globular-structure-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory)

  comp-3-hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory :
    {l1 l2 : Level}
    {x : obj-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory l1}
    {y : obj-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory l2}
    {f g : hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory x y}
    {H K L : 2-hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory f g} →
    3-hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory K L →
    3-hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory H K →
    3-hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory H L
  comp-3-hom-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory =
    comp-3-cell-is-transitive-large-globular-structure
      ( comp-hom-globular-structure-Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory)
```

```agda
open Noncoherent-Large-Wild-⟨∞,∞⟩-Precategory public
```
