# Ideals in rings

```agda
module ring-theory.ideals-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equational-reasoning
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels

open import group-theory.normal-subgroups
open import group-theory.subgroups

open import ring-theory.rings
open import ring-theory.subsets-rings
```

</details>

## Idea

A left ideal of a ring `R` is an additive subgroup of `R` that is closed under
multiplication by elements of `R` from the left.

## Definitions

### Left ideals

```agda
module _
  {l1 : Level} (R : Ring l1)
  where

  is-left-ideal-subset-Ring :
    {l2 : Level} → subset-Ring l2 R → UU (l1 ⊔ l2)
  is-left-ideal-subset-Ring P =
    is-additive-subgroup-subset-Ring R P ×
    is-closed-under-left-multiplication-subset-Ring R P

left-ideal-Ring :
  (l : Level) {l1 : Level} (R : Ring l1) → UU ((lsuc l) ⊔ l1)
left-ideal-Ring l R = Σ (subset-Ring l R) (is-left-ideal-subset-Ring R)

module _
  {l1 l2 : Level} (R : Ring l1) (I : left-ideal-Ring l2 R)
  where

  subset-left-ideal-Ring : subset-Ring l2 R
  subset-left-ideal-Ring = pr1 I

  is-in-left-ideal-Ring : type-Ring R → UU l2
  is-in-left-ideal-Ring x = type-Prop (subset-left-ideal-Ring x)

  type-left-ideal-Ring : UU (l1 ⊔ l2)
  type-left-ideal-Ring = type-subset-Ring R subset-left-ideal-Ring

  inclusion-left-ideal-Ring : type-left-ideal-Ring → type-Ring R
  inclusion-left-ideal-Ring = inclusion-subset-Ring R subset-left-ideal-Ring

  ap-inclusion-left-ideal-Ring :
    (x y : type-left-ideal-Ring) → x ＝ y →
    inclusion-left-ideal-Ring x ＝ inclusion-left-ideal-Ring y
  ap-inclusion-left-ideal-Ring =
    ap-inclusion-subset-Ring R subset-left-ideal-Ring

  is-in-subset-inclusion-left-ideal-Ring :
    (x : type-left-ideal-Ring) →
    is-in-left-ideal-Ring (inclusion-left-ideal-Ring x)
  is-in-subset-inclusion-left-ideal-Ring =
    is-in-subset-inclusion-subset-Ring R subset-left-ideal-Ring

  is-closed-under-eq-left-ideal-Ring :
    {x y : type-Ring R} → is-in-left-ideal-Ring x →
    (x ＝ y) → is-in-left-ideal-Ring y
  is-closed-under-eq-left-ideal-Ring =
    is-closed-under-eq-subset-Ring R subset-left-ideal-Ring

  is-closed-under-eq-left-ideal-Ring' :
    {x y : type-Ring R} → is-in-left-ideal-Ring y →
    (x ＝ y) → is-in-left-ideal-Ring x
  is-closed-under-eq-left-ideal-Ring' =
    is-closed-under-eq-subset-Ring' R subset-left-ideal-Ring

  is-left-ideal-subset-left-ideal-Ring :
    is-left-ideal-subset-Ring R subset-left-ideal-Ring
  is-left-ideal-subset-left-ideal-Ring = pr2 I

  is-additive-subgroup-subset-left-ideal-Ring :
    is-additive-subgroup-subset-Ring R subset-left-ideal-Ring
  is-additive-subgroup-subset-left-ideal-Ring =
    pr1 is-left-ideal-subset-left-ideal-Ring

  contains-zero-left-ideal-Ring : is-in-left-ideal-Ring (zero-Ring R)
  contains-zero-left-ideal-Ring =
    pr1 is-additive-subgroup-subset-left-ideal-Ring

  is-closed-under-addition-left-ideal-Ring :
    is-closed-under-addition-subset-Ring R subset-left-ideal-Ring
  is-closed-under-addition-left-ideal-Ring =
    pr1 (pr2 is-additive-subgroup-subset-left-ideal-Ring)

  is-closed-under-left-multiplication-left-ideal-Ring :
    is-closed-under-left-multiplication-subset-Ring R subset-left-ideal-Ring
  is-closed-under-left-multiplication-left-ideal-Ring =
    pr2 is-left-ideal-subset-left-ideal-Ring
```

### Right ideals

```agda
module _
  {l1 : Level} (R : Ring l1)
  where

  is-right-ideal-subset-Ring :
    {l2 : Level} → subset-Ring l2 R → UU (l1 ⊔ l2)
  is-right-ideal-subset-Ring P =
    is-additive-subgroup-subset-Ring R P ×
    is-closed-under-right-multiplication-subset-Ring R P

right-ideal-Ring :
  (l : Level) {l1 : Level} (R : Ring l1) → UU ((lsuc l) ⊔ l1)
right-ideal-Ring l R = Σ (subset-Ring l R) (is-right-ideal-subset-Ring R)

module _
  {l1 l2 : Level} (R : Ring l1) (I : right-ideal-Ring l2 R)
  where

  subset-right-ideal-Ring : subset-Ring l2 R
  subset-right-ideal-Ring = pr1 I

  is-in-right-ideal-Ring : type-Ring R → UU l2
  is-in-right-ideal-Ring x = type-Prop (subset-right-ideal-Ring x)

  type-right-ideal-Ring : UU (l1 ⊔ l2)
  type-right-ideal-Ring = type-subset-Ring R subset-right-ideal-Ring

  inclusion-right-ideal-Ring : type-right-ideal-Ring → type-Ring R
  inclusion-right-ideal-Ring = inclusion-subset-Ring R subset-right-ideal-Ring

  ap-inclusion-right-ideal-Ring :
    (x y : type-right-ideal-Ring) → x ＝ y →
    inclusion-right-ideal-Ring x ＝ inclusion-right-ideal-Ring y
  ap-inclusion-right-ideal-Ring =
    ap-inclusion-subset-Ring R subset-right-ideal-Ring

  is-in-subset-inclusion-right-ideal-Ring :
    (x : type-right-ideal-Ring) →
    is-in-right-ideal-Ring (inclusion-right-ideal-Ring x)
  is-in-subset-inclusion-right-ideal-Ring =
    is-in-subset-inclusion-subset-Ring R subset-right-ideal-Ring

  is-closed-under-eq-right-ideal-Ring :
    {x y : type-Ring R} → is-in-right-ideal-Ring x →
    (x ＝ y) → is-in-right-ideal-Ring y
  is-closed-under-eq-right-ideal-Ring =
    is-closed-under-eq-subset-Ring R subset-right-ideal-Ring

  is-closed-under-eq-right-ideal-Ring' :
    {x y : type-Ring R} → is-in-right-ideal-Ring y →
    (x ＝ y) → is-in-right-ideal-Ring x
  is-closed-under-eq-right-ideal-Ring' =
    is-closed-under-eq-subset-Ring' R subset-right-ideal-Ring

  is-right-ideal-subset-right-ideal-Ring :
    is-right-ideal-subset-Ring R subset-right-ideal-Ring
  is-right-ideal-subset-right-ideal-Ring = pr2 I

  is-additive-subgroup-subset-right-ideal-Ring :
    is-additive-subgroup-subset-Ring R subset-right-ideal-Ring
  is-additive-subgroup-subset-right-ideal-Ring =
    pr1 is-right-ideal-subset-right-ideal-Ring

  contains-zero-right-ideal-Ring : is-in-right-ideal-Ring (zero-Ring R)
  contains-zero-right-ideal-Ring =
    pr1 is-additive-subgroup-subset-right-ideal-Ring

  is-closed-under-addition-right-ideal-Ring :
    is-closed-under-addition-subset-Ring R subset-right-ideal-Ring
  is-closed-under-addition-right-ideal-Ring =
    pr1 (pr2 is-additive-subgroup-subset-right-ideal-Ring)

  is-closed-under-right-multiplication-right-ideal-Ring :
    is-closed-under-right-multiplication-subset-Ring R subset-right-ideal-Ring
  is-closed-under-right-multiplication-right-ideal-Ring =
    pr2 is-right-ideal-subset-right-ideal-Ring
```

### (Two-sided) ideals

```agda
is-ideal-subset-Ring :
  {l1 l2 : Level} (R : Ring l1) (P : subset-Ring l2 R) → UU (l1 ⊔ l2)
is-ideal-subset-Ring R P =
  is-additive-subgroup-subset-Ring R P ×
  ( is-closed-under-left-multiplication-subset-Ring R P ×
    is-closed-under-right-multiplication-subset-Ring R P)

ideal-Ring :
  (l : Level) {l1 : Level} (R : Ring l1) → UU ((lsuc l) ⊔ l1)
ideal-Ring l R =
  Σ (subset-Ring l R) (is-ideal-subset-Ring R)

module _
  {l1 l2 : Level} (R : Ring l1) (I : ideal-Ring l2 R)
  where

  subset-ideal-Ring : subset-Ring l2 R
  subset-ideal-Ring = pr1 I

  is-in-ideal-Ring : type-Ring R → UU l2
  is-in-ideal-Ring x = type-Prop (subset-ideal-Ring x)

  type-ideal-Ring : UU (l1 ⊔ l2)
  type-ideal-Ring = type-subset-Ring R subset-ideal-Ring

  inclusion-ideal-Ring : type-ideal-Ring → type-Ring R
  inclusion-ideal-Ring =
    inclusion-subset-Ring R subset-ideal-Ring

  ap-inclusion-ideal-Ring :
    (x y : type-ideal-Ring) → x ＝ y →
    inclusion-ideal-Ring x ＝ inclusion-ideal-Ring y
  ap-inclusion-ideal-Ring = ap-inclusion-subset-Ring R subset-ideal-Ring

  is-in-subset-inclusion-ideal-Ring :
    (x : type-ideal-Ring) → is-in-ideal-Ring (inclusion-ideal-Ring x)
  is-in-subset-inclusion-ideal-Ring =
    is-in-subset-inclusion-subset-Ring R subset-ideal-Ring

  is-closed-under-eq-ideal-Ring :
    {x y : type-Ring R} → is-in-ideal-Ring x → (x ＝ y) → is-in-ideal-Ring y
  is-closed-under-eq-ideal-Ring =
    is-closed-under-eq-subset-Ring R subset-ideal-Ring

  is-closed-under-eq-ideal-Ring' :
    {x y : type-Ring R} → is-in-ideal-Ring y → (x ＝ y) → is-in-ideal-Ring x
  is-closed-under-eq-ideal-Ring' =
    is-closed-under-eq-subset-Ring' R subset-ideal-Ring

  is-ideal-subset-ideal-Ring :
    is-ideal-subset-Ring R subset-ideal-Ring
  is-ideal-subset-ideal-Ring = pr2 I

  is-additive-subgroup-subset-ideal-Ring :
    is-additive-subgroup-subset-Ring R subset-ideal-Ring
  is-additive-subgroup-subset-ideal-Ring =
    pr1 is-ideal-subset-ideal-Ring

  contains-zero-ideal-Ring : is-in-ideal-Ring (zero-Ring R)
  contains-zero-ideal-Ring =
    pr1 is-additive-subgroup-subset-ideal-Ring

  is-closed-under-addition-ideal-Ring :
    {x y : type-Ring R} → is-in-ideal-Ring x →
    is-in-ideal-Ring y →
    is-in-ideal-Ring (add-Ring R x y)
  is-closed-under-addition-ideal-Ring H K =
    pr1 (pr2 is-additive-subgroup-subset-ideal-Ring) _ _ H K

  is-closed-under-left-multiplication-ideal-Ring :
    is-closed-under-left-multiplication-subset-Ring R subset-ideal-Ring
  is-closed-under-left-multiplication-ideal-Ring =
    pr1 (pr2 is-ideal-subset-ideal-Ring)

  is-closed-under-neg-ideal-Ring :
    {x : type-Ring R} → is-in-ideal-Ring x →
    is-in-ideal-Ring (neg-Ring R x)
  is-closed-under-neg-ideal-Ring H =
    pr2 (pr2 is-additive-subgroup-subset-ideal-Ring) _ H

  is-closed-under-right-multiplication-ideal-Ring :
    is-closed-under-right-multiplication-subset-Ring R subset-ideal-Ring
  is-closed-under-right-multiplication-ideal-Ring =
    pr2 (pr2 is-ideal-subset-ideal-Ring)

  subgroup-ideal-Ring : Subgroup l2 (group-Ring R)
  pr1 subgroup-ideal-Ring = subset-ideal-Ring
  pr1 (pr2 subgroup-ideal-Ring) = contains-zero-ideal-Ring
  pr1 (pr2 (pr2 subgroup-ideal-Ring)) x y =
    is-closed-under-addition-ideal-Ring
  pr2 (pr2 (pr2 subgroup-ideal-Ring)) x =
    is-closed-under-neg-ideal-Ring

  normal-subgroup-ideal-Ring : Normal-Subgroup l2 (group-Ring R)
  pr1 normal-subgroup-ideal-Ring = subgroup-ideal-Ring
  pr2 normal-subgroup-ideal-Ring x (y , H) =
    tr
      ( is-in-ideal-Ring)
      ( equational-reasoning
          y
          ＝ add-Ring R y (zero-Ring R)
            by inv (right-unit-law-add-Ring R y)
          ＝ add-Ring R y (add-Ring R x (neg-Ring R x))
            by inv (ap (add-Ring R y) (right-inverse-law-add-Ring R x))
          ＝ add-Ring R (add-Ring R y x) (neg-Ring R x)
            by inv (associative-add-Ring R y x (neg-Ring R x))
          ＝ add-Ring R (add-Ring R x y) (neg-Ring R x)
            by ap (add-Ring' R (neg-Ring R x)) (commutative-add-Ring R y x))
      ( H)
```
