# Addition of linear maps between left modules over commutative rings

```agda
module linear-algebra.addition-linear-maps-left-modules-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import foundation.action-on-identifications-binary-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.function-abelian-groups
open import group-theory.subgroups-abelian-groups

open import linear-algebra.addition-linear-maps-left-modules-rings
open import linear-algebra.left-modules-commutative-rings
open import linear-algebra.linear-maps-left-modules-commutative-rings
```

</details>

## Idea

Given two
[linear maps](linear-algebra.linear-maps-left-modules-commutative-rings.md) `f`
and `g` from a [left module](linear-algebra.left-modules-commutative-rings.md)
`M` over a [commutative ring](commutative-algebra.commutative-rings.md) `R` to a
left module `N` over `R`, then the map `x ↦ f x + g x` is a linear map.

## Definition

```agda
module _
  {l1 l2 l3 : Level}
  (R : Commutative-Ring l1)
  (M : left-module-Commutative-Ring l2 R)
  (N : left-module-Commutative-Ring l3 R)
  (f g : linear-map-left-module-Commutative-Ring R M N)
  where

  add-linear-map-left-module-Commutative-Ring :
    linear-map-left-module-Commutative-Ring R M N
  add-linear-map-left-module-Commutative-Ring =
    add-linear-map-left-module-Ring (ring-Commutative-Ring R) M N f g
```

## Properties

### Linear maps form an Abelian group under addition and negation

```agda
module _
  {l1 l2 l3 : Level}
  (R : Commutative-Ring l1)
  (M : left-module-Commutative-Ring l2 R)
  (N : left-module-Commutative-Ring l3 R)
  where

  subgroup-add-linear-map-left-module-Commutative-Ring :
    Subgroup-Ab
      ( l1 ⊔ l2 ⊔ l3)
      ( function-Ab
        ( ab-left-module-Commutative-Ring R N)
        ( type-left-module-Commutative-Ring R M))
  subgroup-add-linear-map-left-module-Commutative-Ring =
    subgroup-add-linear-map-left-module-Ring (ring-Commutative-Ring R) M N

  ab-add-linear-map-left-module-Commutative-Ring : Ab (l1 ⊔ l2 ⊔ l3)
  ab-add-linear-map-left-module-Commutative-Ring =
    ab-add-linear-map-left-module-Ring (ring-Commutative-Ring R) M N
```
