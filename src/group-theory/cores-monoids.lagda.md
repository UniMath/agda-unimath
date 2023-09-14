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

The **core** of a [monoid](group-theory.monoids.md) consists of those elements
that are [invertible](group-theory.invertible-elements-monoids.md).

## Definition

```agda
module _
  {l : Level} (M : Monoid l)
  where

  subtype-core-Monoid : type-Monoid M → Prop l
  subtype-core-Monoid = is-invertible-element-monoid-Prop M

  core-Monoid : Submonoid l M
  pr1 core-Monoid = subtype-core-Monoid
  pr1 (pr2 core-Monoid) = is-invertible-element-unit-Monoid M
  pr2 (pr2 core-Monoid) = is-invertible-element-mul-Monoid M

  monoid-core-Monoid : Monoid l
  monoid-core-Monoid = monoid-Submonoid M core-Monoid

  semigroup-core-Monoid : Semigroup l
  semigroup-core-Monoid = semigroup-Submonoid M core-Monoid

  type-core-Monoid : UU l
  type-core-Monoid =
    type-Submonoid M core-Monoid

  mul-core-Monoid :
    (x y : type-core-Monoid) → type-core-Monoid
  mul-core-Monoid = mul-Submonoid M core-Monoid

  associative-mul-core-Monoid :
    (x y z : type-core-Monoid) →
    mul-core-Monoid (mul-core-Monoid x y) z ＝
    mul-core-Monoid x (mul-core-Monoid y z)
  associative-mul-core-Monoid =
    associative-mul-Submonoid M core-Monoid

  inclusion-core-Monoid :
    type-core-Monoid → type-Monoid M
  inclusion-core-Monoid =
    inclusion-Submonoid M core-Monoid

  preserves-mul-inclusion-core-Monoid :
    (x y : type-core-Monoid) →
    inclusion-core-Monoid (mul-core-Monoid x y) ＝
    mul-Monoid M
      ( inclusion-core-Monoid x)
      ( inclusion-core-Monoid y)
  preserves-mul-inclusion-core-Monoid =
    preserves-mul-inclusion-Submonoid M core-Monoid

  hom-inclusion-core-Monoid :
    type-hom-Monoid monoid-core-Monoid M
  hom-inclusion-core-Monoid =
    hom-inclusion-Submonoid M core-Monoid
```

## Properties

### The core of a monoid is a group

```agda
module _
  {l : Level} (M : Monoid l)
  where

  group-core-Monoid : Group l
  pr1 group-core-Monoid = semigroup-core-Monoid M
  pr1 (pr2 group-core-Monoid) =
    is-unital-semigroup-Monoid (monoid-core-Monoid M)
  pr1 (pr1 (pr2 (pr2 group-core-Monoid)) x) = pr1 (pr2 x)
  pr2 (pr1 (pr2 (pr2 group-core-Monoid)) x) =
    is-invertible-element-inverse-Monoid M (pr1 x) (pr2 x)
  pr1 (pr2 (pr2 (pr2 group-core-Monoid))) x =
    eq-type-subtype (subtype-core-Monoid M) (pr1 (pr2 (pr2 x)))
  pr2 (pr2 (pr2 (pr2 group-core-Monoid))) x =
    eq-type-subtype (subtype-core-Monoid M) (pr2 (pr2 (pr2 x)))
```
