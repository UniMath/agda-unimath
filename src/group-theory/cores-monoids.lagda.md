# Cores of monoids

```agda
module group-theory.cores-monoids where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-large-precategories

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.groups
open import group-theory.homomorphisms-groups
open import group-theory.homomorphisms-monoids
open import group-theory.invertible-elements-monoids
open import group-theory.monoids
open import group-theory.precategory-of-groups
open import group-theory.precategory-of-monoids
open import group-theory.semigroups
open import group-theory.submonoids
```

</details>

## Idea

The **core** of a [monoid](group-theory.monoids.md) `M` is the maximal
[group](group-theory.groups.md) contained in `M`, and consists of all the
elements that are [invertible](group-theory.invertible-elements-monoids.md).

## Definition

```agda
module _
  {l : Level} (M : Monoid l)
  where

  subtype-core-Monoid : type-Monoid M → Prop l
  subtype-core-Monoid = is-invertible-element-prop-Monoid M

  submonoid-core-Monoid : Submonoid l M
  pr1 submonoid-core-Monoid = subtype-core-Monoid
  pr1 (pr2 submonoid-core-Monoid) = is-invertible-element-unit-Monoid M
  pr2 (pr2 submonoid-core-Monoid) = is-invertible-element-mul-Monoid M

  monoid-core-Monoid : Monoid l
  monoid-core-Monoid = monoid-Submonoid M submonoid-core-Monoid

  semigroup-core-Monoid : Semigroup l
  semigroup-core-Monoid = semigroup-Submonoid M submonoid-core-Monoid

  type-core-Monoid : UU l
  type-core-Monoid = type-Submonoid M submonoid-core-Monoid

  mul-core-Monoid : type-core-Monoid → type-core-Monoid → type-core-Monoid
  mul-core-Monoid = mul-Semigroup semigroup-core-Monoid

  associative-mul-core-Monoid :
    (x y z : type-core-Monoid) →
    mul-core-Monoid (mul-core-Monoid x y) z ＝
    mul-core-Monoid x (mul-core-Monoid y z)
  associative-mul-core-Monoid =
    associative-mul-Semigroup semigroup-core-Monoid

  unit-core-Monoid : type-core-Monoid
  pr1 unit-core-Monoid = unit-Monoid M
  pr2 unit-core-Monoid = is-invertible-element-unit-Monoid M

  left-unit-law-mul-core-Monoid :
    (x : type-core-Monoid) →
    mul-core-Monoid unit-core-Monoid x ＝ x
  left-unit-law-mul-core-Monoid x =
    eq-type-subtype subtype-core-Monoid (left-unit-law-mul-Monoid M (pr1 x))

  right-unit-law-mul-core-Monoid :
    (x : type-core-Monoid) →
    mul-core-Monoid x unit-core-Monoid ＝ x
  right-unit-law-mul-core-Monoid x =
    eq-type-subtype subtype-core-Monoid (right-unit-law-mul-Monoid M (pr1 x))

  is-unital-core-Monoid : is-unital-Semigroup semigroup-core-Monoid
  pr1 is-unital-core-Monoid = unit-core-Monoid
  pr1 (pr2 is-unital-core-Monoid) = left-unit-law-mul-core-Monoid
  pr2 (pr2 is-unital-core-Monoid) = right-unit-law-mul-core-Monoid

  inv-core-Monoid : type-core-Monoid → type-core-Monoid
  pr1 (inv-core-Monoid x) =
    inv-is-invertible-element-Monoid M (pr2 x)
  pr2 (inv-core-Monoid x) =
    is-invertible-element-inv-is-invertible-element-Monoid M (pr2 x)

  left-inverse-law-mul-core-Monoid :
    (x : type-core-Monoid) →
    mul-core-Monoid (inv-core-Monoid x) x ＝ unit-core-Monoid
  left-inverse-law-mul-core-Monoid x =
    eq-type-subtype
      ( subtype-core-Monoid)
      ( is-left-inverse-inv-is-invertible-element-Monoid M (pr2 x))

  right-inverse-law-mul-core-Monoid :
    (x : type-core-Monoid) →
    mul-core-Monoid x (inv-core-Monoid x) ＝ unit-core-Monoid
  right-inverse-law-mul-core-Monoid x =
    eq-type-subtype
      ( subtype-core-Monoid)
      ( is-right-inverse-inv-is-invertible-element-Monoid M (pr2 x))

  is-group-core-Monoid' : is-group' semigroup-core-Monoid is-unital-core-Monoid
  pr1 is-group-core-Monoid' = inv-core-Monoid
  pr1 (pr2 is-group-core-Monoid') = left-inverse-law-mul-core-Monoid
  pr2 (pr2 is-group-core-Monoid') = right-inverse-law-mul-core-Monoid

  is-group-core-Monoid : is-group semigroup-core-Monoid
  pr1 is-group-core-Monoid = is-unital-core-Monoid
  pr2 is-group-core-Monoid = is-group-core-Monoid'

  core-Monoid : Group l
  pr1 core-Monoid = semigroup-core-Monoid
  pr2 core-Monoid = is-group-core-Monoid

  inclusion-core-Monoid :
    type-core-Monoid → type-Monoid M
  inclusion-core-Monoid =
    inclusion-Submonoid M submonoid-core-Monoid

  preserves-mul-inclusion-core-Monoid :
    {x y : type-core-Monoid} →
    inclusion-core-Monoid (mul-core-Monoid x y) ＝
    mul-Monoid M
      ( inclusion-core-Monoid x)
      ( inclusion-core-Monoid y)
  preserves-mul-inclusion-core-Monoid {x} {y} =
    preserves-mul-inclusion-Submonoid M submonoid-core-Monoid {x} {y}

  hom-inclusion-core-Monoid :
    hom-Monoid monoid-core-Monoid M
  hom-inclusion-core-Monoid =
    hom-inclusion-Submonoid M submonoid-core-Monoid
```

## Properties

### The core of a monoid is a functor from monoids to groups

#### The functorial action of `core-Monoid`

```agda
module _
  {l1 l2 : Level} (M : Monoid l1) (N : Monoid l2) (f : hom-Monoid M N)
  where

  map-core-hom-Monoid : type-core-Monoid M → type-core-Monoid N
  pr1 (map-core-hom-Monoid x) = map-hom-Monoid M N f (pr1 x)
  pr2 (map-core-hom-Monoid x) =
    preserves-invertible-elements-hom-Monoid M N f (pr2 x)

  preserves-mul-hom-core-hom-Monoid :
    {x y : type-core-Monoid M} →
    map-core-hom-Monoid (mul-core-Monoid M x y) ＝
    mul-core-Monoid N (map-core-hom-Monoid x) (map-core-hom-Monoid y)
  preserves-mul-hom-core-hom-Monoid =
    eq-type-subtype
      ( subtype-core-Monoid N)
      ( preserves-mul-hom-Monoid M N f)

  hom-core-hom-Monoid : hom-Group (core-Monoid M) (core-Monoid N)
  pr1 hom-core-hom-Monoid = map-core-hom-Monoid
  pr2 hom-core-hom-Monoid = preserves-mul-hom-core-hom-Monoid

  preserves-unit-hom-core-hom-Monoid :
    map-core-hom-Monoid (unit-core-Monoid M) ＝ unit-core-Monoid N
  preserves-unit-hom-core-hom-Monoid =
    preserves-unit-hom-Group (core-Monoid M) (core-Monoid N) hom-core-hom-Monoid

  preserves-inv-hom-core-hom-Monoid :
    {x : type-core-Monoid M} →
    map-core-hom-Monoid (inv-core-Monoid M x) ＝
    inv-core-Monoid N (map-core-hom-Monoid x)
  preserves-inv-hom-core-hom-Monoid =
    preserves-inv-hom-Group (core-Monoid M) (core-Monoid N) hom-core-hom-Monoid
```

#### The functorial laws of `core-Monoid`

```agda
module _
  {l : Level} (M : Monoid l)
  where

  preserves-id-hom-core-hom-Monoid :
    hom-core-hom-Monoid M M (id-hom-Monoid M) ＝ id-hom-Group (core-Monoid M)
  preserves-id-hom-core-hom-Monoid =
    eq-htpy-hom-Group
      ( core-Monoid M)
      ( core-Monoid M)
      ( λ _ → eq-type-subtype (subtype-core-Monoid M) refl)

module _
  {l1 l2 l3 : Level} (M : Monoid l1) (N : Monoid l2) (K : Monoid l3)
  where

  preserves-comp-hom-core-hom-Monoid :
    (g : hom-Monoid N K) (f : hom-Monoid M N) →
    hom-core-hom-Monoid M K (comp-hom-Monoid M N K g f) ＝
    comp-hom-Group
      ( core-Monoid M)
      ( core-Monoid N)
      ( core-Monoid K)
      ( hom-core-hom-Monoid N K g)
      ( hom-core-hom-Monoid M N f)
  preserves-comp-hom-core-hom-Monoid g f =
    eq-htpy-hom-Group
      ( core-Monoid M)
      ( core-Monoid K)
      ( λ _ → eq-type-subtype (subtype-core-Monoid K) refl)
```

#### The functor `core-Monoid`

```agda
core-monoid-functor-Large-Precategory :
  functor-Large-Precategory (λ l → l)
    Monoid-Large-Precategory
    Group-Large-Precategory
obj-functor-Large-Precategory
  core-monoid-functor-Large-Precategory =
  core-Monoid
hom-functor-Large-Precategory
  core-monoid-functor-Large-Precategory {X = M} {Y = N} =
  hom-core-hom-Monoid M N
preserves-comp-functor-Large-Precategory
  core-monoid-functor-Large-Precategory {X = M} {Y = N} {Z = K} =
  preserves-comp-hom-core-hom-Monoid M N K
preserves-id-functor-Large-Precategory
  core-monoid-functor-Large-Precategory {X = M} =
  preserves-id-hom-core-hom-Monoid M
```

### The core functor is right adjoint to the forgetful functor from groups to monoids

This remains to be formalized. This forgetful functor also has a left adjoint,
corresponding to _groupification_ of the monoid.
