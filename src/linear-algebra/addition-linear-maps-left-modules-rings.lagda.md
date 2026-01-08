# Addition of linear maps between left modules over rings

```agda
module linear-algebra.addition-linear-maps-left-modules-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.function-abelian-groups
open import group-theory.subgroups-abelian-groups

open import linear-algebra.left-modules-rings
open import linear-algebra.linear-maps-left-modules-rings
open import linear-algebra.negation-linear-maps-left-modules-rings

open import ring-theory.rings
```

</details>

## Idea

Given two [linear maps](linear-algebra.linear-maps-left-modules-rings.md) `f`
and `g` from a [left module](linear-algebra.left-modules-rings.md) `M` over a
[ring](ring-theory.rings.md) `R` to a left module `N` over `R`, the map
`x ↦ f x + g x` is a linear map.

## Definition

```agda
module _
  {l1 l2 l3 : Level}
  (R : Ring l1)
  (M : left-module-Ring l2 R)
  (N : left-module-Ring l3 R)
  (f g : linear-map-left-module-Ring R M N)
  where

  map-add-linear-map-left-module-Ring :
    type-left-module-Ring R M → type-left-module-Ring R N
  map-add-linear-map-left-module-Ring x =
    add-left-module-Ring R N
      ( map-linear-map-left-module-Ring R M N f x)
      ( map-linear-map-left-module-Ring R M N g x)

  abstract
    is-additive-map-add-linear-map-left-module-Ring :
      is-additive-map-left-module-Ring R M N map-add-linear-map-left-module-Ring
    is-additive-map-add-linear-map-left-module-Ring x y =
      ( ap-binary
        ( add-left-module-Ring R N)
        ( is-additive-map-linear-map-left-module-Ring R M N f x y)
        ( is-additive-map-linear-map-left-module-Ring R M N g x y)) ∙
      ( interchange-add-add-left-module-Ring R N _ _ _ _)

    is-homogeneous-map-add-linear-map-left-module-Ring :
      is-homogeneous-map-left-module-Ring R M N
        ( map-add-linear-map-left-module-Ring)
    is-homogeneous-map-add-linear-map-left-module-Ring c x =
      ( ap-binary
        ( add-left-module-Ring R N)
        ( is-homogeneous-map-linear-map-left-module-Ring R M N f c x)
        ( is-homogeneous-map-linear-map-left-module-Ring R M N g c x)) ∙
      ( inv (left-distributive-mul-add-left-module-Ring R N c _ _))

  is-linear-map-add-linear-map-left-module-Ring :
    is-linear-map-left-module-Ring R M N map-add-linear-map-left-module-Ring
  is-linear-map-add-linear-map-left-module-Ring =
    ( is-additive-map-add-linear-map-left-module-Ring ,
      is-homogeneous-map-add-linear-map-left-module-Ring)

  add-linear-map-left-module-Ring : linear-map-left-module-Ring R M N
  add-linear-map-left-module-Ring =
    ( map-add-linear-map-left-module-Ring ,
      is-linear-map-add-linear-map-left-module-Ring)
```

## Properties

### Linear maps form an Abelian group under addition and negation

```agda
module _
  {l1 l2 l3 : Level}
  (R : Ring l1)
  (M : left-module-Ring l2 R)
  (N : left-module-Ring l3 R)
  where

  subgroup-add-linear-map-left-module-Ring :
    Subgroup-Ab
      ( l1 ⊔ l2 ⊔ l3)
      ( function-Ab (ab-left-module-Ring R N) (type-left-module-Ring R M))
  subgroup-add-linear-map-left-module-Ring =
    ( is-linear-map-prop-left-module-Ring R M N ,
      is-linear-const-zero-map-left-module-Ring R M N ,
      ( λ {f} {g} is-linear-f is-linear-g →
        is-linear-map-add-linear-map-left-module-Ring R M N
          ( f , is-linear-f)
          ( g , is-linear-g)) ,
      ( λ {f} is-linear-f →
        is-linear-neg-map-linear-map-left-module-Ring R M N (f , is-linear-f)))

  ab-add-linear-map-left-module-Ring : Ab (l1 ⊔ l2 ⊔ l3)
  ab-add-linear-map-left-module-Ring =
    ab-Subgroup-Ab
      ( function-Ab (ab-left-module-Ring R N) (type-left-module-Ring R M))
      ( subgroup-add-linear-map-left-module-Ring)
```
