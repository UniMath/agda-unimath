# One object precategories

```agda
module category-theory.one-object-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.endomorphisms-in-precategories
open import category-theory.precategories

open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.dependent-products-contractible-types
open import foundation.dependent-products-propositions
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.unit-type
open import foundation.universe-levels

open import group-theory.monoids
```

</details>

## Definition

```agda
is-one-object-prop-Precategory : {l1 l2 : Level} → Precategory l1 l2 → Prop l1
is-one-object-prop-Precategory P = is-contr-Prop (obj-Precategory P)

is-one-object-Precategory : {l1 l2 : Level} → Precategory l1 l2 → UU l1
is-one-object-Precategory P = type-Prop (is-one-object-prop-Precategory P)

One-Object-Precategory : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
One-Object-Precategory l1 l2 = Σ (Precategory l1 l2) (is-one-object-Precategory)

module _
  {l1 l2 : Level} (P : One-Object-Precategory l1 l2)
  where

  precategory-One-Object-Precategory : Precategory l1 l2
  precategory-One-Object-Precategory = pr1 P

  is-one-object-precategory-One-Object-Precategory :
    is-one-object-Precategory precategory-One-Object-Precategory
  is-one-object-precategory-One-Object-Precategory = pr2 P

  object-One-Object-Precategory :
    obj-Precategory precategory-One-Object-Precategory
  object-One-Object-Precategory =
    center is-one-object-precategory-One-Object-Precategory
```

## Properties

### Monoids are one-object precategories

```agda
module _
  {l : Level} (M : Monoid l)
  where

  hom-set-one-object-precategory-Monoid :
    unit → unit → Set l
  hom-set-one-object-precategory-Monoid _ _ = set-Monoid M

  hom-one-object-precategory-Monoid :
    unit → unit → UU l
  hom-one-object-precategory-Monoid x y =
    type-Set (hom-set-one-object-precategory-Monoid x y)

  comp-hom-one-object-precategory-Monoid :
    {x y z : unit} →
    hom-one-object-precategory-Monoid y z →
    hom-one-object-precategory-Monoid x y →
    hom-one-object-precategory-Monoid x z
  comp-hom-one-object-precategory-Monoid =
    mul-Monoid M

  associative-comp-hom-one-object-precategory-Monoid :
    {x y z w : unit} →
    (h : hom-one-object-precategory-Monoid z w)
    (g : hom-one-object-precategory-Monoid y z)
    (f : hom-one-object-precategory-Monoid x y) →
    comp-hom-one-object-precategory-Monoid
      ( comp-hom-one-object-precategory-Monoid h g)
      ( f) ＝
    comp-hom-one-object-precategory-Monoid
      ( h)
      ( comp-hom-one-object-precategory-Monoid g f)
  associative-comp-hom-one-object-precategory-Monoid =
    associative-mul-Monoid M

  id-hom-one-object-precategory-Monoid :
    (x : unit) → hom-one-object-precategory-Monoid x x
  id-hom-one-object-precategory-Monoid _ = unit-Monoid M

  left-unit-law-comp-hom-one-object-precategory-Monoid :
    {x y : unit} (f : hom-one-object-precategory-Monoid x y) →
    comp-hom-one-object-precategory-Monoid
      ( id-hom-one-object-precategory-Monoid y)
      ( f) ＝
    f
  left-unit-law-comp-hom-one-object-precategory-Monoid =
    left-unit-law-mul-Monoid M

  right-unit-law-comp-hom-one-object-precategory-Monoid :
    {x y : unit} (f : hom-one-object-precategory-Monoid x y) →
    comp-hom-one-object-precategory-Monoid
      ( f)
      ( id-hom-one-object-precategory-Monoid x) ＝
    f
  right-unit-law-comp-hom-one-object-precategory-Monoid =
    right-unit-law-mul-Monoid M

  precategory-one-object-precategory-Monoid : Precategory lzero l
  precategory-one-object-precategory-Monoid =
    make-Precategory
      ( unit)
      ( hom-set-one-object-precategory-Monoid)
      ( comp-hom-one-object-precategory-Monoid)
      ( id-hom-one-object-precategory-Monoid)
      ( associative-comp-hom-one-object-precategory-Monoid)
      ( left-unit-law-comp-hom-one-object-precategory-Monoid)
      ( right-unit-law-comp-hom-one-object-precategory-Monoid)

  one-object-precategory-Monoid : One-Object-Precategory lzero l
  pr1 one-object-precategory-Monoid = precategory-one-object-precategory-Monoid
  pr2 one-object-precategory-Monoid = is-contr-unit
```

### Monoids from one-object precategories

```agda
monoid-One-Object-Precategory :
  {l1 l2 : Level} → One-Object-Precategory l1 l2 → Monoid l2
monoid-One-Object-Precategory P =
  monoid-endo-Precategory
    ( precategory-One-Object-Precategory P)
    ( object-One-Object-Precategory P)
```
