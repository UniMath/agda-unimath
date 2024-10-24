# Noncoherent wild higher precategories

```agda
{-# OPTIONS --guardedness #-}

module wild-category-theory.noncoherent-wild-higher-precategories where
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

open import structured-types.globular-types
open import structured-types.reflexive-globular-types
open import structured-types.transitive-globular-types
```

</details>

## Idea

It is an important open problem known as the _coherence problem_ to define a
fully coherent notion of $∞$-category in univalent type theory. The subject of
_wild category theory_ attempts to recover some of the benefits of $∞$-category
theory without tackling this problem. We introduce, as one of our basic building
blocks in this subject, the notion of a _noncoherent wild higher precategory_.

A _noncoherent wild higher precategory_ `𝒞` is a structure that attempts at
capturing the structure of a higher precategory to the $0$'th order. It consists
of in some sense all of the operations and none of the coherence of a higher
precategory. Thus, it is defined as a
[globular type](structured-types.globular-types.md) with families of
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
{{#concept "noncoherent wild higher precategory" Agda=Noncoherent-Wild-Higher-Precategory}}
to be a [reflexive](structured-types.reflexive-globular-types.md) and
[transitive](structured-types.transitive-globular-types.md) globular type. We
call the 0-cells the _objects_, the 1-cells the _morphisms_ and the higher cells
the _$n$-morphisms_. The reflexivities are called the _identity morphisms_, and
the transitivity operations are branded as _composition of morphisms_.

## Definitions

### Noncoherent wild higher precategories

```agda
Noncoherent-Wild-Higher-Precategory : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Noncoherent-Wild-Higher-Precategory l1 l2 =
  Σ ( Globular-Type l1 l2)
    ( λ X → is-reflexive-Globular-Type X × is-transitive-Globular-Type X)

make-Noncoherent-Wild-Higher-Precategory :
  {l1 l2 : Level} {X : Globular-Type l1 l2} → is-reflexive-Globular-Type X →
  is-transitive-Globular-Type X → Noncoherent-Wild-Higher-Precategory l1 l2
make-Noncoherent-Wild-Higher-Precategory id comp =
  ( _ , id , comp)

{-# INLINE make-Noncoherent-Wild-Higher-Precategory #-}

module _
  {l1 l2 : Level} (𝒞 : Noncoherent-Wild-Higher-Precategory l1 l2)
  where

  globular-type-Noncoherent-Wild-Higher-Precategory : Globular-Type l1 l2
  globular-type-Noncoherent-Wild-Higher-Precategory = pr1 𝒞

  obj-Noncoherent-Wild-Higher-Precategory : UU l1
  obj-Noncoherent-Wild-Higher-Precategory =
    0-cell-Globular-Type globular-type-Noncoherent-Wild-Higher-Precategory
```

- Morphisms in a noncoherent wild higher precategory

```agda
  hom-globular-type-Noncoherent-Wild-Higher-Precategory :
    (x y : obj-Noncoherent-Wild-Higher-Precategory) →
    Globular-Type l2 l2
  hom-globular-type-Noncoherent-Wild-Higher-Precategory =
    1-cell-globular-type-Globular-Type
      globular-type-Noncoherent-Wild-Higher-Precategory

  hom-Noncoherent-Wild-Higher-Precategory :
    obj-Noncoherent-Wild-Higher-Precategory →
    obj-Noncoherent-Wild-Higher-Precategory →
    UU l2
  hom-Noncoherent-Wild-Higher-Precategory =
    1-cell-Globular-Type globular-type-Noncoherent-Wild-Higher-Precategory
```

- Identity morphisms in a noncoherent wild higher precategory

```agda
  id-structure-Noncoherent-Wild-Higher-Precategory :
    is-reflexive-Globular-Type globular-type-Noncoherent-Wild-Higher-Precategory
  id-structure-Noncoherent-Wild-Higher-Precategory =
    pr1 (pr2 𝒞)

  id-hom-Noncoherent-Wild-Higher-Precategory :
    {x : obj-Noncoherent-Wild-Higher-Precategory} →
    hom-Noncoherent-Wild-Higher-Precategory x x
  id-hom-Noncoherent-Wild-Higher-Precategory {x} =
    refl-2-cell-is-reflexive-Globular-Type
      id-structure-Noncoherent-Wild-Higher-Precategory

  id-structure-hom-globular-type-Noncoherent-Wild-Higher-Precategory :
    {x y : obj-Noncoherent-Wild-Higher-Precategory} →
    is-reflexive-Globular-Type
      ( hom-globular-type-Noncoherent-Wild-Higher-Precategory x y)
  id-structure-hom-globular-type-Noncoherent-Wild-Higher-Precategory =
    is-reflexive-1-cell-globular-type-is-reflexive-Globular-Type
      id-structure-Noncoherent-Wild-Higher-Precategory

  reflexive-globular-type-Noncoherent-Wild-Higher-Precategory :
    Reflexive-Globular-Type l1 l2
  globular-type-Reflexive-Globular-Type
    reflexive-globular-type-Noncoherent-Wild-Higher-Precategory =
    globular-type-Noncoherent-Wild-Higher-Precategory
  refl-Reflexive-Globular-Type
    reflexive-globular-type-Noncoherent-Wild-Higher-Precategory =
    id-structure-Noncoherent-Wild-Higher-Precategory

  hom-reflexive-globular-type-Noncoherent-Wild-Higher-Precategory :
    (x y : obj-Noncoherent-Wild-Higher-Precategory) →
    Reflexive-Globular-Type l2 l2
  hom-reflexive-globular-type-Noncoherent-Wild-Higher-Precategory x y =
    1-cell-reflexive-globular-type-Reflexive-Globular-Type
      ( reflexive-globular-type-Noncoherent-Wild-Higher-Precategory)
      ( x)
      ( y)
```

- Composition in a noncoherent wild higher precategory

```agda
  comp-structure-Noncoherent-Wild-Higher-Precategory :
    is-transitive-Globular-Type
      globular-type-Noncoherent-Wild-Higher-Precategory
  comp-structure-Noncoherent-Wild-Higher-Precategory =
    pr2 (pr2 𝒞)

  comp-hom-Noncoherent-Wild-Higher-Precategory :
    {x y z : obj-Noncoherent-Wild-Higher-Precategory} →
    hom-Noncoherent-Wild-Higher-Precategory y z →
    hom-Noncoherent-Wild-Higher-Precategory x y →
    hom-Noncoherent-Wild-Higher-Precategory x z
  comp-hom-Noncoherent-Wild-Higher-Precategory =
    comp-1-cell-is-transitive-Globular-Type
      comp-structure-Noncoherent-Wild-Higher-Precategory

  comp-structure-hom-globular-type-Noncoherent-Wild-Higher-Precategory :
    {x y : obj-Noncoherent-Wild-Higher-Precategory} →
    is-transitive-Globular-Type
      ( hom-globular-type-Noncoherent-Wild-Higher-Precategory x y)
  comp-structure-hom-globular-type-Noncoherent-Wild-Higher-Precategory =
    is-transitive-1-cell-globular-type-is-transitive-Globular-Type
      comp-structure-Noncoherent-Wild-Higher-Precategory

  transitive-globular-type-Noncoherent-Wild-Higher-Precategory :
    Transitive-Globular-Type l1 l2
  globular-type-Transitive-Globular-Type
    transitive-globular-type-Noncoherent-Wild-Higher-Precategory =
    globular-type-Noncoherent-Wild-Higher-Precategory
  is-transitive-Transitive-Globular-Type
    transitive-globular-type-Noncoherent-Wild-Higher-Precategory =
    comp-structure-Noncoherent-Wild-Higher-Precategory

  hom-transitive-globular-type-Noncoherent-Wild-Higher-Precategory :
    (x y : obj-Noncoherent-Wild-Higher-Precategory) →
    Transitive-Globular-Type l2 l2
  hom-transitive-globular-type-Noncoherent-Wild-Higher-Precategory x y =
    1-cell-transitive-globular-type-Transitive-Globular-Type
      ( transitive-globular-type-Noncoherent-Wild-Higher-Precategory)
      ( x)
      ( y)
```

- The noncoherent wild higher precategory of morphisms between two objects in a
  noncoherent wild higher precategory

```agda
  hom-noncoherent-wild-higher-precategory-Noncoherent-Wild-Higher-Precategory :
    (x y : obj-Noncoherent-Wild-Higher-Precategory) →
    Noncoherent-Wild-Higher-Precategory l2 l2
  hom-noncoherent-wild-higher-precategory-Noncoherent-Wild-Higher-Precategory
    x y =
    make-Noncoherent-Wild-Higher-Precategory
      ( id-structure-hom-globular-type-Noncoherent-Wild-Higher-Precategory
        {x} {y})
      ( comp-structure-hom-globular-type-Noncoherent-Wild-Higher-Precategory)
```

- 2-Morphisms in a noncoherent wild higher precategory

```agda
  2-hom-Noncoherent-Wild-Higher-Precategory :
    {x y : obj-Noncoherent-Wild-Higher-Precategory} →
    hom-Noncoherent-Wild-Higher-Precategory x y →
    hom-Noncoherent-Wild-Higher-Precategory x y →
    UU l2
  2-hom-Noncoherent-Wild-Higher-Precategory =
    2-cell-Globular-Type globular-type-Noncoherent-Wild-Higher-Precategory

  id-2-hom-Noncoherent-Wild-Higher-Precategory :
    {x y : obj-Noncoherent-Wild-Higher-Precategory}
    {f : hom-Noncoherent-Wild-Higher-Precategory x y} →
    2-hom-Noncoherent-Wild-Higher-Precategory f f
  id-2-hom-Noncoherent-Wild-Higher-Precategory =
    refl-3-cell-is-reflexive-Globular-Type
      id-structure-Noncoherent-Wild-Higher-Precategory

  comp-2-hom-Noncoherent-Wild-Higher-Precategory :
    {x y : obj-Noncoherent-Wild-Higher-Precategory}
    {f g h : hom-Noncoherent-Wild-Higher-Precategory x y} →
    2-hom-Noncoherent-Wild-Higher-Precategory g h →
    2-hom-Noncoherent-Wild-Higher-Precategory f g →
    2-hom-Noncoherent-Wild-Higher-Precategory f h
  comp-2-hom-Noncoherent-Wild-Higher-Precategory =
    comp-2-cell-is-transitive-Globular-Type
      comp-structure-Noncoherent-Wild-Higher-Precategory
```

- 3-Morphisms in a noncoherent wild higher precategory

```agda
  3-hom-Noncoherent-Wild-Higher-Precategory :
    {x y : obj-Noncoherent-Wild-Higher-Precategory}
    {f g : hom-Noncoherent-Wild-Higher-Precategory x y} →
    2-hom-Noncoherent-Wild-Higher-Precategory f g →
    2-hom-Noncoherent-Wild-Higher-Precategory f g → UU l2
  3-hom-Noncoherent-Wild-Higher-Precategory =
    3-cell-Globular-Type globular-type-Noncoherent-Wild-Higher-Precategory

  id-3-hom-Noncoherent-Wild-Higher-Precategory :
    {x y : obj-Noncoherent-Wild-Higher-Precategory}
    {f g : hom-Noncoherent-Wild-Higher-Precategory x y}
    {H : 2-hom-Noncoherent-Wild-Higher-Precategory f g} →
    3-hom-Noncoherent-Wild-Higher-Precategory H H
  id-3-hom-Noncoherent-Wild-Higher-Precategory =
    refl-4-cell-is-reflexive-Globular-Type
      globular-type-Noncoherent-Wild-Higher-Precategory
      id-structure-Noncoherent-Wild-Higher-Precategory

  comp-3-hom-Noncoherent-Wild-Higher-Precategory :
    {x y : obj-Noncoherent-Wild-Higher-Precategory}
    {f g : hom-Noncoherent-Wild-Higher-Precategory x y}
    {H K L : 2-hom-Noncoherent-Wild-Higher-Precategory f g} →
    3-hom-Noncoherent-Wild-Higher-Precategory K L →
    3-hom-Noncoherent-Wild-Higher-Precategory H K →
    3-hom-Noncoherent-Wild-Higher-Precategory H L
  comp-3-hom-Noncoherent-Wild-Higher-Precategory =
    comp-3-cell-is-transitive-Globular-Type
      comp-structure-Noncoherent-Wild-Higher-Precategory
```
