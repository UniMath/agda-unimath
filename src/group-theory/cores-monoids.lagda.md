# Core of a monoid

```agda
module group-theory.cores-monoids where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.groups
open import group-theory.homomorphisms-monoids
open import group-theory.invertible-elements-monoids
open import group-theory.monoids
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
  subtype-core-Monoid = is-invertible-element-monoid-Prop M

  submonoid-core-Monoid : Submonoid l M
  pr1 submonoid-core-Monoid = subtype-core-Monoid
  pr1 (pr2 submonoid-core-Monoid) = is-invertible-element-unit-Monoid M
  pr2 (pr2 submonoid-core-Monoid) = is-invertible-element-mul-Monoid M

  monoid-core-Monoid : Monoid l
  monoid-core-Monoid = monoid-Submonoid M submonoid-core-Monoid

  semigroup-core-Monoid : Semigroup l
  semigroup-core-Monoid = semigroup-Submonoid M submonoid-core-Monoid

  type-core-Monoid : UU l
  type-core-Monoid =
    type-Submonoid M submonoid-core-Monoid

  core-Monoid : Group l
  pr1 core-Monoid = semigroup-core-Monoid
  pr1 (pr2 core-Monoid) =
    is-unital-semigroup-Monoid monoid-core-Monoid
  pr1 (pr1 (pr2 (pr2 core-Monoid)) x) = pr1 (pr2 x)
  pr2 (pr1 (pr2 (pr2 core-Monoid)) x) =
    is-invertible-element-inverse-Monoid M (pr1 x) (pr2 x)
  pr1 (pr2 (pr2 (pr2 core-Monoid))) x =
    eq-type-subtype subtype-core-Monoid (pr1 (pr2 (pr2 x)))
  pr2 (pr2 (pr2 (pr2 core-Monoid))) x =
    eq-type-subtype subtype-core-Monoid (pr2 (pr2 (pr2 x)))

  mul-core-Monoid :
    (x y : type-core-Monoid) → type-core-Monoid
  mul-core-Monoid =
    mul-Submonoid M submonoid-core-Monoid

  associative-mul-core-Monoid :
    (x y z : type-core-Monoid) →
    mul-core-Monoid (mul-core-Monoid x y) z ＝
    mul-core-Monoid x (mul-core-Monoid y z)
  associative-mul-core-Monoid =
    associative-mul-Submonoid M submonoid-core-Monoid

  inclusion-core-Monoid :
    type-core-Monoid → type-Monoid M
  inclusion-core-Monoid =
    inclusion-Submonoid M submonoid-core-Monoid

  preserves-mul-inclusion-core-Monoid :
    (x y : type-core-Monoid) →
    inclusion-core-Monoid (mul-core-Monoid x y) ＝
    mul-Monoid M
      ( inclusion-core-Monoid x)
      ( inclusion-core-Monoid y)
  preserves-mul-inclusion-core-Monoid =
    preserves-mul-inclusion-Submonoid M submonoid-core-Monoid

  hom-inclusion-core-Monoid :
    type-hom-Monoid monoid-core-Monoid M
  hom-inclusion-core-Monoid =
    hom-inclusion-Submonoid M submonoid-core-Monoid
```

## Properties

### The core of a monoid is a functorial construction

This remains to be formalized.

### The core functor is left adjoint to the forgetful functor from groups to monoids

This remains to be formalized. This forgetful functor also admits a further
right adjoint, corresponding to _groupification_ of the monoid.
