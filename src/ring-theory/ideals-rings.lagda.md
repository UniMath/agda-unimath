# Ideals in rings

```agda
module ring-theory.ideals-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.equational-reasoning
open import foundation.existential-quantification
open import foundation.fibers-of-maps
open import foundation.functions
open import foundation.identity-types
open import foundation.propositional-extensionality
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.normal-subgroups
open import group-theory.subgroups
open import group-theory.subgroups-abelian-groups

open import ring-theory.rings
open import ring-theory.subsets-rings

open import univalent-combinatorics.lists
```

</details>

## Idea

A left ideal of a ring `R` is an additive subgroup of `R` that is closed under multiplication by elements of `R` from the left.

## Definitions

### Additive subgroups

```agda
module _
  {l1 : Level} (R : Ring l1)
  where

  is-additive-subgroup-subset-Ring :
    {l2 : Level} → subset-Ring l2 R → UU (l1 ⊔ l2)
  is-additive-subgroup-subset-Ring = is-subgroup-Ab (ab-Ring R)
```

### Left ideals

```agda
module _
  {l1 : Level} (R : Ring l1)
  where

  is-closed-under-mul-left-subset-Ring :
    {l2 : Level} → subset-Ring l2 R → UU (l1 ⊔ l2)
  is-closed-under-mul-left-subset-Ring P =
    (x : type-Ring R) (y : type-Ring R) →
    type-Prop (P y) → type-Prop (P (mul-Ring R x y))

  is-left-ideal-subset-Ring :
    {l2 : Level} → subset-Ring l2 R → UU (l1 ⊔ l2)
  is-left-ideal-subset-Ring P =
    is-additive-subgroup-subset-Ring R P ×
    is-closed-under-mul-left-subset-Ring P

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

  is-closed-under-add-left-ideal-Ring :
    {x y : type-Ring R} → is-in-left-ideal-Ring x → is-in-left-ideal-Ring y →
    is-in-left-ideal-Ring (add-Ring R x y)
  is-closed-under-add-left-ideal-Ring H K =
    pr1 (pr2 is-additive-subgroup-subset-left-ideal-Ring) _ _ H K

  is-closed-under-mul-left-ideal-Ring :
    is-closed-under-mul-left-subset-Ring R subset-left-ideal-Ring
  is-closed-under-mul-left-ideal-Ring =
    pr2 is-left-ideal-subset-left-ideal-Ring
```

### Right ideals

```agda
module _
  {l1 : Level} (R : Ring l1)
  where

  is-closed-under-mul-right-subset-Ring :
    {l2 : Level} → subset-Ring l2 R → UU (l1 ⊔ l2)
  is-closed-under-mul-right-subset-Ring P =
    (x : type-Ring R) (y : type-Ring R) →
    type-Prop (P x) → type-Prop (P (mul-Ring R x y))

  is-right-ideal-subset-Ring :
    {l2 : Level} → subset-Ring l2 R → UU (l1 ⊔ l2)
  is-right-ideal-subset-Ring P =
    is-additive-subgroup-subset-Ring R P ×
    is-closed-under-mul-right-subset-Ring P

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

  is-closed-under-add-right-ideal-Ring :
    {x y : type-Ring R} → is-in-right-ideal-Ring x → is-in-right-ideal-Ring y →
    is-in-right-ideal-Ring (add-Ring R x y)
  is-closed-under-add-right-ideal-Ring H K =
    pr1 (pr2 is-additive-subgroup-subset-right-ideal-Ring) _ _ H K

  is-closed-under-mul-right-ideal-Ring :
    is-closed-under-mul-right-subset-Ring R subset-right-ideal-Ring
  is-closed-under-mul-right-ideal-Ring =
    pr2 is-right-ideal-subset-right-ideal-Ring
```

### Two-sided ideals

```agda
is-two-sided-ideal-subset-Ring :
  {l1 l2 : Level} (R : Ring l1) (P : subset-Ring l2 R) → UU (l1 ⊔ l2)
is-two-sided-ideal-subset-Ring R P =
  is-additive-subgroup-subset-Ring R P ×
  ( is-closed-under-mul-left-subset-Ring R P ×
    is-closed-under-mul-right-subset-Ring R P)

two-sided-ideal-Ring :
  (l : Level) {l1 : Level} (R : Ring l1) → UU ((lsuc l) ⊔ l1)
two-sided-ideal-Ring l R =
  Σ (subset-Ring l R) (is-two-sided-ideal-subset-Ring R)

module _
  {l1 l2 : Level} (R : Ring l1) (I : two-sided-ideal-Ring l2 R)
  where

  subset-two-sided-ideal-Ring : subset-Ring l2 R
  subset-two-sided-ideal-Ring = pr1 I

  is-in-two-sided-ideal-Ring : type-Ring R → UU l2
  is-in-two-sided-ideal-Ring x = type-Prop (subset-two-sided-ideal-Ring x)

  type-two-sided-ideal-Ring : UU (l1 ⊔ l2)
  type-two-sided-ideal-Ring = type-subset-Ring R subset-two-sided-ideal-Ring

  inclusion-two-sided-ideal-Ring : type-two-sided-ideal-Ring → type-Ring R
  inclusion-two-sided-ideal-Ring =
    inclusion-subset-Ring R subset-two-sided-ideal-Ring

  is-two-sided-ideal-subset-two-sided-ideal-Ring :
    is-two-sided-ideal-subset-Ring R subset-two-sided-ideal-Ring
  is-two-sided-ideal-subset-two-sided-ideal-Ring = pr2 I

  is-additive-subgroup-subset-two-sided-ideal-Ring :
    is-additive-subgroup-subset-Ring R subset-two-sided-ideal-Ring
  is-additive-subgroup-subset-two-sided-ideal-Ring =
    pr1 is-two-sided-ideal-subset-two-sided-ideal-Ring

  contains-zero-two-sided-ideal-Ring : is-in-two-sided-ideal-Ring (zero-Ring R)
  contains-zero-two-sided-ideal-Ring =
    pr1 is-additive-subgroup-subset-two-sided-ideal-Ring

  is-closed-under-add-two-sided-ideal-Ring :
    {x y : type-Ring R} → is-in-two-sided-ideal-Ring x →
    is-in-two-sided-ideal-Ring y →
    is-in-two-sided-ideal-Ring (add-Ring R x y)
  is-closed-under-add-two-sided-ideal-Ring H K =
    pr1 (pr2 is-additive-subgroup-subset-two-sided-ideal-Ring) _ _ H K

  is-closed-under-mul-left-two-sided-ideal-Ring :
    is-closed-under-mul-left-subset-Ring R subset-two-sided-ideal-Ring
  is-closed-under-mul-left-two-sided-ideal-Ring =
    pr1 (pr2 is-two-sided-ideal-subset-two-sided-ideal-Ring)

  is-closed-under-neg-two-sided-ideal-Ring :
    {x : type-Ring R} → is-in-two-sided-ideal-Ring x →
    is-in-two-sided-ideal-Ring (neg-Ring R x)
  is-closed-under-neg-two-sided-ideal-Ring H =
    pr2 (pr2 is-additive-subgroup-subset-two-sided-ideal-Ring) _ H

  is-closed-under-mul-right-two-sided-ideal-Ring :
    is-closed-under-mul-right-subset-Ring R subset-two-sided-ideal-Ring
  is-closed-under-mul-right-two-sided-ideal-Ring =
    pr2 (pr2 is-two-sided-ideal-subset-two-sided-ideal-Ring)

  subgroup-two-sided-ideal-Ring : Subgroup l2 (group-Ring R)
  pr1 subgroup-two-sided-ideal-Ring = subset-two-sided-ideal-Ring
  pr1 (pr2 subgroup-two-sided-ideal-Ring) = contains-zero-two-sided-ideal-Ring
  pr1 (pr2 (pr2 subgroup-two-sided-ideal-Ring)) x y = is-closed-under-add-two-sided-ideal-Ring
  pr2 (pr2 (pr2 subgroup-two-sided-ideal-Ring)) x = is-closed-under-neg-two-sided-ideal-Ring

  normal-subgroup-two-sided-ideal-Ring : Normal-Subgroup l2 (group-Ring R)
  pr1 normal-subgroup-two-sided-ideal-Ring = subgroup-two-sided-ideal-Ring
  pr2 normal-subgroup-two-sided-ideal-Ring x (y , H) =
    tr
      ( is-in-two-sided-ideal-Ring)
      ( equational-reasoning
        y
        ＝ add-Ring R y (zero-Ring R)                 by inv (right-unit-law-add-Ring R y)
        ＝ add-Ring R y (add-Ring R x (neg-Ring R x)) by inv (ap (add-Ring R y) (right-inverse-law-add-Ring R x))
        ＝ add-Ring R (add-Ring R y x) (neg-Ring R x) by inv (associative-add-Ring R y x (neg-Ring R x))
        ＝ add-Ring R (add-Ring R x y) (neg-Ring R x) by ap (add-Ring' R (neg-Ring R x)) (commutative-add-Ring R y x))
      ( H)
```
