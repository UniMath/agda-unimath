# Large preorders

```agda
module order-theory.large-preorders where
```

<details><summary>Imports</summary>

```agda
open import category-theory.large-precategories

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.large-binary-relations
open import foundation.propositions
open import foundation.sets
open import foundation.strictly-involutive-identity-types
open import foundation.universe-levels

open import order-theory.preorders
```

</details>

## Idea

A **large preorder** consists of types indexed by a universe levels, and an
ordering relation comparing objects of arbitrary universe levels. This level of
generality therefore accommodates the inclusion relation on subtypes of
different universe levels. Many [preorders](order-theory.preorders.md) in
agda-unimath naturally arise as large preorders.

## Definitions

### Large preorders

```agda
record
  Large-Preorder (α : Level → Level) (β : Level → Level → Level) : UUω
  where
  eta-equality
  constructor
    make-Large-Preorder
  field
    type-Large-Preorder : (l : Level) → UU (α l)
    leq-prop-Large-Preorder : Large-Relation-Prop β type-Large-Preorder
    refl-leq-Large-Preorder :
      is-reflexive-Large-Relation-Prop
        ( type-Large-Preorder)
        ( leq-prop-Large-Preorder)
    transitive-leq-Large-Preorder :
      is-transitive-Large-Relation-Prop
        ( type-Large-Preorder)
        ( leq-prop-Large-Preorder)

open Large-Preorder public

module _
  {α : Level → Level} {β : Level → Level → Level} (X : Large-Preorder α β)
  where

  leq-Large-Preorder : Large-Relation β (type-Large-Preorder X)
  leq-Large-Preorder =
    large-relation-Large-Relation-Prop
      ( type-Large-Preorder X)
      ( leq-prop-Large-Preorder X)

  is-prop-leq-Large-Preorder :
    is-prop-Large-Relation (type-Large-Preorder X) (leq-Large-Preorder)
  is-prop-leq-Large-Preorder =
    is-prop-large-relation-Large-Relation-Prop
      ( type-Large-Preorder X)
      ( leq-prop-Large-Preorder X)

  leq-eq-Large-Preorder :
    {l1 : Level}
    {x y : type-Large-Preorder X l1} →
    (x ＝ y) → leq-Large-Preorder x y
  leq-eq-Large-Preorder {x = x} refl = refl-leq-Large-Preorder X x
```

### The predicate on large precategories to be a large preorder

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Precategory α β)
  where

  is-large-preorder-Large-Precategory : UUω
  is-large-preorder-Large-Precategory =
    {l1 l2 : Level}
    (X : obj-Large-Precategory C l1) (Y : obj-Large-Precategory C l2) →
    is-prop (hom-Large-Precategory C X Y)

  large-preorder-Large-Precategory :
    is-large-preorder-Large-Precategory → Large-Preorder α β
  type-Large-Preorder
    ( large-preorder-Large-Precategory H) =
    obj-Large-Precategory C
  pr1 (leq-prop-Large-Preorder (large-preorder-Large-Precategory H) X Y) =
    hom-Large-Precategory C X Y
  pr2 (leq-prop-Large-Preorder (large-preorder-Large-Precategory H) X Y) =
    H X Y
  refl-leq-Large-Preorder
    ( large-preorder-Large-Precategory H)
    ( X) =
    id-hom-Large-Precategory C
  transitive-leq-Large-Preorder
    ( large-preorder-Large-Precategory H)
    ( X)
    ( Y)
    ( Z) =
    comp-hom-Large-Precategory C
```

## Properties

### Small preorders from large preorders

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (P : Large-Preorder α β)
  where

  preorder-Large-Preorder : (l : Level) → Preorder (α l) (β l l)
  pr1 (preorder-Large-Preorder l) = type-Large-Preorder P l
  pr1 (pr2 (preorder-Large-Preorder l)) = leq-prop-Large-Preorder P
  pr1 (pr2 (pr2 (preorder-Large-Preorder l))) = refl-leq-Large-Preorder P
  pr2 (pr2 (pr2 (preorder-Large-Preorder l))) = transitive-leq-Large-Preorder P
```

### Large preorders are large precategories

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (P : Large-Preorder α β)
  where

  large-precategory-Large-Preorder : Large-Precategory α β
  obj-Large-Precategory large-precategory-Large-Preorder = type-Large-Preorder P
  hom-set-Large-Precategory large-precategory-Large-Preorder x y =
    set-Prop (leq-prop-Large-Preorder P x y)
  comp-hom-Large-Precategory large-precategory-Large-Preorder {X = x} {y} {z} =
    transitive-leq-Large-Preorder P x y z
  id-hom-Large-Precategory large-precategory-Large-Preorder {X = x} =
    refl-leq-Large-Preorder P x
  involutive-eq-associative-comp-hom-Large-Precategory
    large-precategory-Large-Preorder
    {X = x} {W = w} h g f =
    involutive-eq-eq (eq-is-prop (is-prop-leq-Large-Preorder P x w))
  left-unit-law-comp-hom-Large-Precategory large-precategory-Large-Preorder
    {X = x} {y} f =
    eq-is-prop (is-prop-leq-Large-Preorder P x y)
  right-unit-law-comp-hom-Large-Precategory large-precategory-Large-Preorder
    {X = x} {y} f =
    eq-is-prop (is-prop-leq-Large-Preorder P x y)
```
