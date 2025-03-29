# Linear maps between modules over rings

```agda
module ring-theory.linear-maps-modules-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import group-theory.abelian-groups

open import ring-theory.modules-rings
open import ring-theory.rings
```

</details>

## Idea

## Definition

```agda
module _
  {l1 l2 l3 : Level} (R : Ring l1)
  (M : left-module-Ring l2 R) (N : left-module-Ring l3 R)
  (f : type-left-module-Ring R M → type-left-module-Ring R N)
  where

  is-additive-map-prop-left-module-Ring : Prop (l2 ⊔ l3)
  is-additive-map-prop-left-module-Ring =
    Π-Prop
      ( type-left-module-Ring R M)
      ( λ x →
        Π-Prop
          ( type-left-module-Ring R M)
          ( λ y →
            Id-Prop
              ( set-left-module-Ring R N)
              ( f (add-left-module-Ring R M x y))
              ( add-left-module-Ring R N (f x) (f y))))

  is-additive-map-left-module-Ring : UU (l2 ⊔ l3)
  is-additive-map-left-module-Ring =
    type-Prop is-additive-map-prop-left-module-Ring

  is-homogenous-map-prop-left-module-Ring : Prop (l1 ⊔ l2 ⊔ l3)
  is-homogenous-map-prop-left-module-Ring =
    Π-Prop
      ( type-Ring R)
      ( λ c →
        Π-Prop
          ( type-left-module-Ring R M)
          ( λ x →
            Id-Prop
              ( set-left-module-Ring R N)
              ( f (mul-left-module-Ring R M c x))
              ( mul-left-module-Ring R N c (f x))))

  is-homogenous-map-left-module-Ring : UU (l1 ⊔ l2 ⊔ l3)
  is-homogenous-map-left-module-Ring =
    type-Prop is-homogenous-map-prop-left-module-Ring

  is-linear-map-prop-left-module-Ring : Prop (l1 ⊔ l2 ⊔ l3)
  is-linear-map-prop-left-module-Ring =
    is-additive-map-prop-left-module-Ring ∧
    is-homogenous-map-prop-left-module-Ring

  is-linear-map-left-module-Ring : UU (l1 ⊔ l2 ⊔ l3)
  is-linear-map-left-module-Ring =
    type-Prop is-linear-map-prop-left-module-Ring

  is-additive-is-linear-map-left-module-Ring :
    is-linear-map-left-module-Ring →
    (x y : type-left-module-Ring R M) →
    f (add-left-module-Ring R M x y) ＝
    add-left-module-Ring R N (f x) (f y)
  is-additive-is-linear-map-left-module-Ring = pr1

  is-homogenous-is-linear-map-left-module-Ring :
    is-linear-map-left-module-Ring →
    (c : type-Ring R) (x : type-left-module-Ring R M) →
    f (mul-left-module-Ring R M c x) ＝
    mul-left-module-Ring R N c (f x)
  is-homogenous-is-linear-map-left-module-Ring = pr2

  is-zero-map-zero-is-homogenous-map-left-module-Ring :
    is-homogenous-map-left-module-Ring →
    f (zero-left-module-Ring R M) ＝ zero-left-module-Ring R N
  is-zero-map-zero-is-homogenous-map-left-module-Ring K =
    equational-reasoning
      f (zero-left-module-Ring R M)
      ＝ f (mul-left-module-Ring R M (zero-Ring R) (zero-left-module-Ring R M))
        by ap f (inv (left-zero-law-mul-left-module-Ring R M _))
      ＝ mul-left-module-Ring R N (zero-Ring R) (f (zero-left-module-Ring R M))
        by K _ _
      ＝ zero-left-module-Ring R N
        by left-zero-law-mul-left-module-Ring R N _

  is-zero-map-zero-is-linear-map-left-module-Ring :
    is-linear-map-left-module-Ring →
    f (zero-left-module-Ring R M) ＝ zero-left-module-Ring R N
  is-zero-map-zero-is-linear-map-left-module-Ring H =
    is-zero-map-zero-is-homogenous-map-left-module-Ring
      (is-homogenous-is-linear-map-left-module-Ring H)
```
