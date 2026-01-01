# Center of a monoid

```agda
module group-theory.centers-monoids where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels

open import group-theory.centers-semigroups
open import group-theory.central-elements-monoids
open import group-theory.commutative-monoids
open import group-theory.homomorphisms-monoids
open import group-theory.monoids
open import group-theory.submonoids
```

</details>

## Idea

The {{#concept "center" Disambiguation="of a monoid" Agda=center-Monoid}} of a
[monoid](group-theory.monoids.md) `M` is the
[submonoid](group-theory.submonoids.md) consisting of those elements of `M`
which are [central](group-theory.central-elements-monoids.md).

## Definition

```agda
module _
  {l : Level} (M : Monoid l)
  where

  subtype-center-Monoid : type-Monoid M → Prop l
  subtype-center-Monoid = is-central-element-prop-Monoid M

  center-Monoid : Submonoid l M
  pr1 center-Monoid = subtype-center-Monoid
  pr1 (pr2 center-Monoid) = is-central-element-unit-Monoid M
  pr2 (pr2 center-Monoid) = is-central-element-mul-Monoid M

  monoid-center-Monoid : Monoid l
  monoid-center-Monoid = monoid-Submonoid M center-Monoid

  type-center-Monoid : UU l
  type-center-Monoid =
    type-Submonoid M center-Monoid

  mul-center-Monoid :
    (x y : type-center-Monoid) → type-center-Monoid
  mul-center-Monoid = mul-Submonoid M center-Monoid

  associative-mul-center-Monoid :
    (x y z : type-center-Monoid) →
    mul-center-Monoid (mul-center-Monoid x y) z ＝
    mul-center-Monoid x (mul-center-Monoid y z)
  associative-mul-center-Monoid =
    associative-mul-Submonoid M center-Monoid

  inclusion-center-Monoid :
    type-center-Monoid → type-Monoid M
  inclusion-center-Monoid =
    inclusion-Submonoid M center-Monoid

  preserves-mul-inclusion-center-Monoid :
    {x y : type-center-Monoid} →
    inclusion-center-Monoid (mul-center-Monoid x y) ＝
    mul-Monoid M
      ( inclusion-center-Monoid x)
      ( inclusion-center-Monoid y)
  preserves-mul-inclusion-center-Monoid {x} {y} =
    preserves-mul-inclusion-Submonoid M center-Monoid {x} {y}

  hom-inclusion-center-Monoid :
    hom-Monoid monoid-center-Monoid M
  hom-inclusion-center-Monoid =
    hom-inclusion-Submonoid M center-Monoid

  abstract
    commutative-mul-center-Monoid :
      (x y : type-center-Monoid) →
      mul-center-Monoid x y ＝ mul-center-Monoid y x
    commutative-mul-center-Monoid =
      commutative-mul-center-Semigroup (semigroup-Monoid M)

  commutative-monoid-center-Monoid : Commutative-Monoid l
  commutative-monoid-center-Monoid =
    ( monoid-center-Monoid ,
      commutative-mul-center-Monoid)
```
