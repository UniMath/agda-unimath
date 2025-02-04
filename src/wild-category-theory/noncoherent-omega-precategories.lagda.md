# Noncoherent ω-precategories

```agda
{-# OPTIONS --guardedness #-}

module wild-category-theory.noncoherent-omega-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.precategories

open import foundation.action-on-identifications-binary-functions
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.sets
open import foundation.strictly-involutive-identity-types
open import foundation.universe-levels

open import globular-types.globular-types
open import globular-types.reflexive-globular-types
open import globular-types.transitive-globular-types
```

</details>

## Idea

It is an important open problem known as the _coherence problem_ to define a
fully coherent notion of $∞$-category or higher variants in univalent type
theory. The subject of _wild category theory_ attempts to recover some of the
benefits of $∞$-category theory without tackling this problem. We introduce, as
one of our basic building blocks in this subject, the notion of a _noncoherent
ω-precategory_.

A _noncoherent ω-precategory_ `𝒞` is a structure that attempts at capturing the
structure of an ω-category to the $0$'th order. It consists of in some sense all
of the operations and none of the coherence. Thus, it is defined as a
[globular type](globular-types.globular-types.md) with families of $n$-morphisms
labeled as "identities"

```text
  id-hom : (x : 𝒞ₙ) → 𝒞ₙ₊₁ x x
```

and a composition operation at every dimension

```text
  comp-hom : {x y z : 𝒞ₙ} → 𝒞ₙ₊₁ y z → 𝒞ₙ₊₁ x y → 𝒞ₙ₊₁ x z.
```

Entirely concretely, we define a
{{#concept "noncoherent ω-precategory" Agda=Noncoherent-ω-Precategory}} to be a
[reflexive](globular-types.reflexive-globular-types.md) and
[transitive](globular-types.transitive-globular-types.md) globular type. We call
the 0-cells the _objects_, the 1-cells the _morphisms_ and the higher cells the
_$n$-morphisms_. The reflexivities are called the _identity morphisms_, and the
transitivity operations are branded as _composition of morphisms_.

## Definitions

### Noncoherent ω-precategories

```agda
Noncoherent-ω-Precategory : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Noncoherent-ω-Precategory l1 l2 =
  Σ ( Globular-Type l1 l2)
    ( λ X → is-reflexive-Globular-Type X × is-transitive-Globular-Type X)

make-Noncoherent-ω-Precategory :
  {l1 l2 : Level} {X : Globular-Type l1 l2} → is-reflexive-Globular-Type X →
  is-transitive-Globular-Type X → Noncoherent-ω-Precategory l1 l2
make-Noncoherent-ω-Precategory id comp =
  ( _ , id , comp)

{-# INLINE make-Noncoherent-ω-Precategory #-}

module _
  {l1 l2 : Level} (𝒞 : Noncoherent-ω-Precategory l1 l2)
  where

  globular-type-Noncoherent-ω-Precategory : Globular-Type l1 l2
  globular-type-Noncoherent-ω-Precategory = pr1 𝒞

  obj-Noncoherent-ω-Precategory : UU l1
  obj-Noncoherent-ω-Precategory =
    0-cell-Globular-Type globular-type-Noncoherent-ω-Precategory
```

Morphisms in a noncoherent ω-precategory:

```agda
  hom-globular-type-Noncoherent-ω-Precategory :
    (x y : obj-Noncoherent-ω-Precategory) →
    Globular-Type l2 l2
  hom-globular-type-Noncoherent-ω-Precategory =
    1-cell-globular-type-Globular-Type
      globular-type-Noncoherent-ω-Precategory

  hom-Noncoherent-ω-Precategory :
    obj-Noncoherent-ω-Precategory →
    obj-Noncoherent-ω-Precategory →
    UU l2
  hom-Noncoherent-ω-Precategory =
    1-cell-Globular-Type globular-type-Noncoherent-ω-Precategory
```

Identity morphisms in a noncoherent ω-precategory:

```agda
  id-structure-Noncoherent-ω-Precategory :
    is-reflexive-Globular-Type globular-type-Noncoherent-ω-Precategory
  id-structure-Noncoherent-ω-Precategory =
    pr1 (pr2 𝒞)

  id-hom-Noncoherent-ω-Precategory :
    {x : obj-Noncoherent-ω-Precategory} →
    hom-Noncoherent-ω-Precategory x x
  id-hom-Noncoherent-ω-Precategory {x} =
    refl-2-cell-is-reflexive-Globular-Type
      id-structure-Noncoherent-ω-Precategory

  id-structure-hom-globular-type-Noncoherent-ω-Precategory :
    {x y : obj-Noncoherent-ω-Precategory} →
    is-reflexive-Globular-Type
      ( hom-globular-type-Noncoherent-ω-Precategory x y)
  id-structure-hom-globular-type-Noncoherent-ω-Precategory =
    is-reflexive-1-cell-globular-type-is-reflexive-Globular-Type
      id-structure-Noncoherent-ω-Precategory

  reflexive-globular-type-Noncoherent-ω-Precategory :
    Reflexive-Globular-Type l1 l2
  globular-type-Reflexive-Globular-Type
    reflexive-globular-type-Noncoherent-ω-Precategory =
    globular-type-Noncoherent-ω-Precategory
  refl-Reflexive-Globular-Type
    reflexive-globular-type-Noncoherent-ω-Precategory =
    id-structure-Noncoherent-ω-Precategory

  hom-reflexive-globular-type-Noncoherent-ω-Precategory :
    (x y : obj-Noncoherent-ω-Precategory) →
    Reflexive-Globular-Type l2 l2
  hom-reflexive-globular-type-Noncoherent-ω-Precategory x y =
    1-cell-reflexive-globular-type-Reflexive-Globular-Type
      ( reflexive-globular-type-Noncoherent-ω-Precategory)
      ( x)
      ( y)
```

Composition in a noncoherent ω-precategory:

```agda
  comp-structure-Noncoherent-ω-Precategory :
    is-transitive-Globular-Type
      globular-type-Noncoherent-ω-Precategory
  comp-structure-Noncoherent-ω-Precategory =
    pr2 (pr2 𝒞)

  comp-hom-Noncoherent-ω-Precategory :
    {x y z : obj-Noncoherent-ω-Precategory} →
    hom-Noncoherent-ω-Precategory y z →
    hom-Noncoherent-ω-Precategory x y →
    hom-Noncoherent-ω-Precategory x z
  comp-hom-Noncoherent-ω-Precategory =
    comp-1-cell-is-transitive-Globular-Type
      comp-structure-Noncoherent-ω-Precategory

  comp-structure-hom-globular-type-Noncoherent-ω-Precategory :
    {x y : obj-Noncoherent-ω-Precategory} →
    is-transitive-Globular-Type
      ( hom-globular-type-Noncoherent-ω-Precategory x y)
  comp-structure-hom-globular-type-Noncoherent-ω-Precategory =
    is-transitive-1-cell-globular-type-is-transitive-Globular-Type
      comp-structure-Noncoherent-ω-Precategory

  transitive-globular-type-Noncoherent-ω-Precategory :
    Transitive-Globular-Type l1 l2
  globular-type-Transitive-Globular-Type
    transitive-globular-type-Noncoherent-ω-Precategory =
    globular-type-Noncoherent-ω-Precategory
  is-transitive-Transitive-Globular-Type
    transitive-globular-type-Noncoherent-ω-Precategory =
    comp-structure-Noncoherent-ω-Precategory

  hom-transitive-globular-type-Noncoherent-ω-Precategory :
    (x y : obj-Noncoherent-ω-Precategory) →
    Transitive-Globular-Type l2 l2
  hom-transitive-globular-type-Noncoherent-ω-Precategory x y =
    1-cell-transitive-globular-type-Transitive-Globular-Type
      ( transitive-globular-type-Noncoherent-ω-Precategory)
      ( x)
      ( y)
```

The noncoherent ω-precategory of morphisms between two objects in a noncoherent
ω-precategory:

```agda
  hom-noncoherent-ω-precategory-Noncoherent-ω-Precategory :
    (x y : obj-Noncoherent-ω-Precategory) →
    Noncoherent-ω-Precategory l2 l2
  hom-noncoherent-ω-precategory-Noncoherent-ω-Precategory
    x y =
    make-Noncoherent-ω-Precategory
      ( id-structure-hom-globular-type-Noncoherent-ω-Precategory
        {x} {y})
      ( comp-structure-hom-globular-type-Noncoherent-ω-Precategory)
```

2-Morphisms in a noncoherent ω-precategory:

```agda
  2-hom-Noncoherent-ω-Precategory :
    {x y : obj-Noncoherent-ω-Precategory} →
    hom-Noncoherent-ω-Precategory x y →
    hom-Noncoherent-ω-Precategory x y →
    UU l2
  2-hom-Noncoherent-ω-Precategory =
    2-cell-Globular-Type globular-type-Noncoherent-ω-Precategory

  id-2-hom-Noncoherent-ω-Precategory :
    {x y : obj-Noncoherent-ω-Precategory}
    {f : hom-Noncoherent-ω-Precategory x y} →
    2-hom-Noncoherent-ω-Precategory f f
  id-2-hom-Noncoherent-ω-Precategory =
    refl-3-cell-is-reflexive-Globular-Type
      id-structure-Noncoherent-ω-Precategory

  comp-2-hom-Noncoherent-ω-Precategory :
    {x y : obj-Noncoherent-ω-Precategory}
    {f g h : hom-Noncoherent-ω-Precategory x y} →
    2-hom-Noncoherent-ω-Precategory g h →
    2-hom-Noncoherent-ω-Precategory f g →
    2-hom-Noncoherent-ω-Precategory f h
  comp-2-hom-Noncoherent-ω-Precategory =
    comp-2-cell-is-transitive-Globular-Type
      comp-structure-Noncoherent-ω-Precategory
```

3-Morphisms in a noncoherent ω-precategory:

```agda
  3-hom-Noncoherent-ω-Precategory :
    {x y : obj-Noncoherent-ω-Precategory}
    {f g : hom-Noncoherent-ω-Precategory x y} →
    2-hom-Noncoherent-ω-Precategory f g →
    2-hom-Noncoherent-ω-Precategory f g → UU l2
  3-hom-Noncoherent-ω-Precategory =
    3-cell-Globular-Type globular-type-Noncoherent-ω-Precategory

  id-3-hom-Noncoherent-ω-Precategory :
    {x y : obj-Noncoherent-ω-Precategory}
    {f g : hom-Noncoherent-ω-Precategory x y}
    {H : 2-hom-Noncoherent-ω-Precategory f g} →
    3-hom-Noncoherent-ω-Precategory H H
  id-3-hom-Noncoherent-ω-Precategory =
    refl-4-cell-is-reflexive-Globular-Type
      globular-type-Noncoherent-ω-Precategory
      id-structure-Noncoherent-ω-Precategory

  comp-3-hom-Noncoherent-ω-Precategory :
    {x y : obj-Noncoherent-ω-Precategory}
    {f g : hom-Noncoherent-ω-Precategory x y}
    {H K L : 2-hom-Noncoherent-ω-Precategory f g} →
    3-hom-Noncoherent-ω-Precategory K L →
    3-hom-Noncoherent-ω-Precategory H K →
    3-hom-Noncoherent-ω-Precategory H L
  comp-3-hom-Noncoherent-ω-Precategory =
    comp-3-cell-is-transitive-Globular-Type
      comp-structure-Noncoherent-ω-Precategory
```
