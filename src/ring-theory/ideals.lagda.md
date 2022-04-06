---
title: Ideals in rings
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module ring-theory.ideals where

open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.existential-quantification
open import foundation.fibers-of-maps
open import foundation.identity-types
open import foundation.propositional-extensionality
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.abelian-subgroups

open import ring-theory.rings
open import ring-theory.subsets-rings

open import univalent-combinatorics.lists
```

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

  is-closed-under-mul-left-two-sided-ideal-Ring :
    is-closed-under-mul-left-subset-Ring R subset-two-sided-ideal-Ring
  is-closed-under-mul-left-two-sided-ideal-Ring =
    pr1 (pr2 is-two-sided-ideal-subset-two-sided-ideal-Ring)

  is-closed-under-mul-right-two-sided-ideal-Ring :
    is-closed-under-mul-right-subset-Ring R subset-two-sided-ideal-Ring
  is-closed-under-mul-right-two-sided-ideal-Ring =
    pr2 (pr2 is-two-sided-ideal-subset-two-sided-ideal-Ring)
```

### Left ideals generated by a subset of a ring

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (S : subset-Ring l2 R)
  where

  formal-combination-subset-Ring : UU (l1 ⊔ l2)
  formal-combination-subset-Ring = list (type-Ring R × type-subset-Ring R S)

  ev-formal-combination-subset-Ring :
    formal-combination-subset-Ring → type-Ring R
  ev-formal-combination-subset-Ring nil = zero-Ring R
  ev-formal-combination-subset-Ring (cons (pair r s) l) =
    add-Ring R
      ( mul-Ring R r (inclusion-subset-Ring R S s))
      ( ev-formal-combination-subset-Ring l)

  preserves-concat-ev-formal-combination-subset-Ring :
    (u v : formal-combination-subset-Ring) →
    Id ( ev-formal-combination-subset-Ring (concat-list u v))
       ( add-Ring R
         ( ev-formal-combination-subset-Ring u)
         ( ev-formal-combination-subset-Ring v))
  preserves-concat-ev-formal-combination-subset-Ring nil v =
    inv (left-unit-law-add-Ring R (ev-formal-combination-subset-Ring v))
  preserves-concat-ev-formal-combination-subset-Ring (cons (pair r s) u) v =
    ( ap
      ( add-Ring R (mul-Ring R r (inclusion-subset-Ring R S s)))
      ( preserves-concat-ev-formal-combination-subset-Ring u v)) ∙
    ( inv
      ( associative-add-Ring R
        ( mul-Ring R r (inclusion-subset-Ring R S s))
        ( ev-formal-combination-subset-Ring u)
        ( ev-formal-combination-subset-Ring v)))

  mul-formal-combination-subset-Ring :
    type-Ring R →
    formal-combination-subset-Ring → formal-combination-subset-Ring
  mul-formal-combination-subset-Ring r =
    map-list (λ x → pair (mul-Ring R r (pr1 x)) (pr2 x))

  preserves-mul-ev-formal-combination-subset-Ring :
    (r : type-Ring R) (u : formal-combination-subset-Ring) →
    Id ( ev-formal-combination-subset-Ring
         ( mul-formal-combination-subset-Ring r u))
       ( mul-Ring R r (ev-formal-combination-subset-Ring u))
  preserves-mul-ev-formal-combination-subset-Ring r nil =
    inv (right-zero-law-mul-Ring R r)
  preserves-mul-ev-formal-combination-subset-Ring r (cons x u) =
    ( ap-add-Ring R
      ( associative-mul-Ring R r (pr1 x) (inclusion-subset-Ring R S (pr2 x)))
      ( preserves-mul-ev-formal-combination-subset-Ring r u)) ∙
    ( inv
      ( left-distributive-mul-add-Ring R r
        ( mul-Ring R (pr1 x) (inclusion-subset-Ring R S (pr2 x)))
        ( ev-formal-combination-subset-Ring u)))

  subset-left-ideal-subset-Ring' : type-Ring R → UU (l1 ⊔ l2)
  subset-left-ideal-subset-Ring' x =
    fib ev-formal-combination-subset-Ring x

  subset-left-ideal-subset-Ring : subset-Ring (l1 ⊔ l2) R
  subset-left-ideal-subset-Ring x =
    trunc-Prop (subset-left-ideal-subset-Ring' x)

  contains-zero-left-ideal-subset-Ring :
    type-Prop (subset-left-ideal-subset-Ring (zero-Ring R))
  contains-zero-left-ideal-subset-Ring = unit-trunc-Prop (pair nil refl)

  closed-under-addition-left-ideal-subset-Ring' :
    (x y : type-Ring R) →
    subset-left-ideal-subset-Ring' x → subset-left-ideal-subset-Ring' y →
    subset-left-ideal-subset-Ring' (add-Ring R x y)
  pr1
    ( closed-under-addition-left-ideal-subset-Ring' x y (pair l p) (pair k q)) =
    concat-list l k
  pr2
    ( closed-under-addition-left-ideal-subset-Ring' x y (pair l p) (pair k q)) =
    ( preserves-concat-ev-formal-combination-subset-Ring l k) ∙
    ( ap-add-Ring R p q)
  
  -- closed-under-addition-left-ideal-subset-Ring :
  --   (x y : type-Ring R) →
  --   type-Prop (subset-left-ideal-subset-Ring x) →
  --   type-Prop (subset-left-ideal-subset-Ring y) →
  --   type-Prop (subset-left-ideal-subset-Ring (add-Ring R x y))
  -- closed-under-addition-left-ideal-subset-Ring x y H K =
  --   apply-universal-property-trunc-Prop H
  --     ( subset-left-ideal-subset-Ring (add-Ring R x y))
  --     ( λ H' →
  --       apply-universal-property-trunc-Prop K
  --         ( subset-left-ideal-subset-Ring (add-Ring R x y))
  --         ( λ K' →
  --           unit-trunc-Prop
  --             ( closed-under-addition-left-ideal-subset-Ring' x y H' K')))

  -- closed-under-mul-left-ideal-subset-Ring' :
  --   (r x : type-Ring R) → subset-left-ideal-subset-Ring' x →
  --   subset-left-ideal-subset-Ring' (mul-Ring R r x)
  -- pr1 (closed-under-mul-left-ideal-subset-Ring' r x (pair l p)) =
  --   map-list ((λ u → pair (mul-Ring R r (pr1 u)) (pr2 u))) l
  -- pr2 (closed-under-mul-left-ideal-subset-Ring' r x (pair l p)) = {!!}
  
  -- -- left-ideal-subset-Ring : left-ideal-Ring (l1 ⊔ l2) R
  -- -- pr1 left-ideal-subset-Ring = subset-left-ideal-subset-Ring
  -- -- pr1 (pr1 (pr2 left-ideal-subset-Ring)) = contains-zero-left-ideal-subset-Ring
  -- -- pr1 (pr2 (pr1 (pr2 left-ideal-subset-Ring))) =
  -- --   {!!}
  -- -- pr2 (pr2 (pr1 (pr2 left-ideal-subset-Ring))) = {!!}
  -- -- pr2 (pr2 left-ideal-subset-Ring) = {!!}
