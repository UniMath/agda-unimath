# Gaunt precategories

```agda
module category-theory.gaunt-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.composition-operations-on-binary-families-of-sets
open import category-theory.isomorphisms-in-precategories
open import category-theory.precategories

open import foundation.1-types
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels
```

</details>

## Idea

A **gaunt precategory** is a [precategory](category-theory.precategories.md) for
which the
[isomorphism](category-theory.isomorphisms-in-precategories.md)-[sets](foundation-core.sets.md)
are [propositions](foundation-core.propositions.md).

## Definitions

### The predicate on precategories of being gaunt

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  where

  is-gaunt-prop-Precategory : Prop (l1 ⊔ l2)
  is-gaunt-prop-Precategory =
    Π-Prop
      ( obj-Precategory C)
      ( λ x →
        Π-Prop
          ( obj-Precategory C)
          ( λ y → is-prop-Prop (iso-Precategory C x y)))

  is-gaunt-Precategory : UU (l1 ⊔ l2)
  is-gaunt-Precategory = type-Prop is-gaunt-prop-Precategory
```

### The type of gaunt precategories

```agda
Gaunt-Precategory : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Gaunt-Precategory l1 l2 =
  Σ (Precategory l1 l2) (is-gaunt-Precategory)

module _
  {l1 l2 : Level} (C : Gaunt-Precategory l1 l2)
  where

  precategory-Gaunt-Precategory : Precategory l1 l2
  precategory-Gaunt-Precategory = pr1 C

  obj-Gaunt-Precategory : UU l1
  obj-Gaunt-Precategory = obj-Precategory precategory-Gaunt-Precategory

  hom-set-Gaunt-Precategory :
    obj-Gaunt-Precategory → obj-Gaunt-Precategory → Set l2
  hom-set-Gaunt-Precategory =
    hom-set-Precategory precategory-Gaunt-Precategory

  hom-Gaunt-Precategory :
    obj-Gaunt-Precategory → obj-Gaunt-Precategory → UU l2
  hom-Gaunt-Precategory = hom-Precategory precategory-Gaunt-Precategory

  is-set-hom-Gaunt-Precategory :
    (x y : obj-Gaunt-Precategory) → is-set (hom-Gaunt-Precategory x y)
  is-set-hom-Gaunt-Precategory =
    is-set-hom-Precategory precategory-Gaunt-Precategory

  comp-hom-Gaunt-Precategory :
    {x y z : obj-Gaunt-Precategory} →
    hom-Gaunt-Precategory y z →
    hom-Gaunt-Precategory x y →
    hom-Gaunt-Precategory x z
  comp-hom-Gaunt-Precategory =
    comp-hom-Precategory precategory-Gaunt-Precategory

  associative-comp-hom-Gaunt-Precategory :
    {x y z w : obj-Gaunt-Precategory}
    (h : hom-Gaunt-Precategory z w)
    (g : hom-Gaunt-Precategory y z)
    (f : hom-Gaunt-Precategory x y) →
    comp-hom-Gaunt-Precategory (comp-hom-Gaunt-Precategory h g) f ＝
    comp-hom-Gaunt-Precategory h (comp-hom-Gaunt-Precategory g f)
  associative-comp-hom-Gaunt-Precategory =
    associative-comp-hom-Precategory precategory-Gaunt-Precategory

  associative-composition-operation-Gaunt-Precategory :
    associative-composition-operation-binary-family-Set
      hom-set-Gaunt-Precategory
  associative-composition-operation-Gaunt-Precategory =
    associative-composition-operation-Precategory
      ( precategory-Gaunt-Precategory)

  id-hom-Gaunt-Precategory :
    {x : obj-Gaunt-Precategory} → hom-Gaunt-Precategory x x
  id-hom-Gaunt-Precategory =
    id-hom-Precategory precategory-Gaunt-Precategory

  left-unit-law-comp-hom-Gaunt-Precategory :
    {x y : obj-Gaunt-Precategory} (f : hom-Gaunt-Precategory x y) →
    comp-hom-Gaunt-Precategory id-hom-Gaunt-Precategory f ＝ f
  left-unit-law-comp-hom-Gaunt-Precategory =
    left-unit-law-comp-hom-Precategory precategory-Gaunt-Precategory

  right-unit-law-comp-hom-Gaunt-Precategory :
    {x y : obj-Gaunt-Precategory} (f : hom-Gaunt-Precategory x y) →
    comp-hom-Gaunt-Precategory f id-hom-Gaunt-Precategory ＝ f
  right-unit-law-comp-hom-Gaunt-Precategory =
    right-unit-law-comp-hom-Precategory precategory-Gaunt-Precategory

  is-unital-composition-operation-Gaunt-Precategory :
    is-unital-composition-operation-binary-family-Set
      hom-set-Gaunt-Precategory
      comp-hom-Gaunt-Precategory
  is-unital-composition-operation-Gaunt-Precategory =
    is-unital-composition-operation-Precategory
      ( precategory-Gaunt-Precategory)

  is-gaunt-Gaunt-Precategory :
    is-gaunt-Precategory precategory-Gaunt-Precategory
  is-gaunt-Gaunt-Precategory = pr2 C
```

### The total hom-type of a gaunt category

```agda
total-hom-Gaunt-Precategory :
  {l1 l2 : Level} (C : Gaunt-Precategory l1 l2) → UU (l1 ⊔ l2)
total-hom-Gaunt-Precategory C =
  total-hom-Precategory (precategory-Gaunt-Precategory C)

obj-total-hom-Gaunt-Precategory :
  {l1 l2 : Level} (C : Gaunt-Precategory l1 l2) →
  total-hom-Gaunt-Precategory C →
  obj-Gaunt-Precategory C × obj-Gaunt-Precategory C
obj-total-hom-Gaunt-Precategory C =
  obj-total-hom-Precategory (precategory-Gaunt-Precategory C)
```

### Equalities induce morphisms

```agda
module _
  {l1 l2 : Level}
  (C : Gaunt-Precategory l1 l2)
  where

  hom-eq-Gaunt-Precategory :
    (x y : obj-Gaunt-Precategory C) →
    x ＝ y → hom-Gaunt-Precategory C x y
  hom-eq-Gaunt-Precategory =
    hom-eq-Precategory (precategory-Gaunt-Precategory C)

  hom-inv-eq-Gaunt-Precategory :
    (x y : obj-Gaunt-Precategory C) →
    x ＝ y → hom-Gaunt-Precategory C y x
  hom-inv-eq-Gaunt-Precategory =
    hom-inv-eq-Precategory (precategory-Gaunt-Precategory C)
```

### Pre- and postcomposition by a morphism

```agda
precomp-hom-Gaunt-Precategory :
  {l1 l2 : Level} (C : Gaunt-Precategory l1 l2)
  {x y : obj-Gaunt-Precategory C}
  (f : hom-Gaunt-Precategory C x y)
  (z : obj-Gaunt-Precategory C) →
  hom-Gaunt-Precategory C y z →
  hom-Gaunt-Precategory C x z
precomp-hom-Gaunt-Precategory C =
  precomp-hom-Precategory (precategory-Gaunt-Precategory C)

postcomp-hom-Gaunt-Precategory :
  {l1 l2 : Level} (C : Gaunt-Precategory l1 l2)
  {x y : obj-Gaunt-Precategory C}
  (f : hom-Gaunt-Precategory C x y)
  (z : obj-Gaunt-Precategory C) →
  hom-Gaunt-Precategory C z x →
  hom-Gaunt-Precategory C z y
postcomp-hom-Gaunt-Precategory C =
  postcomp-hom-Precategory (precategory-Gaunt-Precategory C)
```
