# Ideals in semirings

```agda
module ring-theory.ideals-semirings where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equational-reasoning
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels

open import group-theory.submonoids

open import ring-theory.semirings
open import ring-theory.subsets-semirings
```

</details>

## Idea

A left ideal of a semiring `R` is an additive subgroup of `R` that is closed under multiplication by elements of `R` from the left.

## Definitions

### Additive submonoids

```agda
module _
  {l1 : Level} (R : Semiring l1)
  where

  is-additive-submonoid-Semiring :
    {l2 : Level} → subset-Semiring l2 R → UU (l1 ⊔ l2)
  is-additive-submonoid-Semiring =
    is-submonoid-Monoid (additive-monoid-Semiring R)
```

### Left ideals

```agda
module _
  {l1 : Level} (R : Semiring l1)
  where

  is-closed-under-mul-left-subset-Semiring :
    {l2 : Level} → subset-Semiring l2 R → UU (l1 ⊔ l2)
  is-closed-under-mul-left-subset-Semiring P =
    (x : type-Semiring R) (y : type-Semiring R) →
    type-Prop (P y) → type-Prop (P (mul-Semiring R x y))

  is-left-ideal-subset-Semiring :
    {l2 : Level} → subset-Semiring l2 R → UU (l1 ⊔ l2)
  is-left-ideal-subset-Semiring P =
    is-additive-submonoid-Semiring R P ×
    is-closed-under-mul-left-subset-Semiring P

left-ideal-Semiring :
  (l : Level) {l1 : Level} (R : Semiring l1) → UU ((lsuc l) ⊔ l1)
left-ideal-Semiring l R =
  Σ (subset-Semiring l R) (is-left-ideal-subset-Semiring R)

module _
  {l1 l2 : Level} (R : Semiring l1) (I : left-ideal-Semiring l2 R)
  where

  subset-left-ideal-Semiring : subset-Semiring l2 R
  subset-left-ideal-Semiring = pr1 I

  is-in-left-ideal-Semiring : type-Semiring R → UU l2
  is-in-left-ideal-Semiring x = type-Prop (subset-left-ideal-Semiring x)

  type-left-ideal-Semiring : UU (l1 ⊔ l2)
  type-left-ideal-Semiring = type-subset-Semiring R subset-left-ideal-Semiring

  inclusion-left-ideal-Semiring : type-left-ideal-Semiring → type-Semiring R
  inclusion-left-ideal-Semiring =
    inclusion-subset-Semiring R subset-left-ideal-Semiring

  is-left-ideal-subset-left-ideal-Semiring :
    is-left-ideal-subset-Semiring R subset-left-ideal-Semiring
  is-left-ideal-subset-left-ideal-Semiring = pr2 I

  is-additive-submonoid-left-ideal-Semiring :
    is-additive-submonoid-Semiring R subset-left-ideal-Semiring
  is-additive-submonoid-left-ideal-Semiring =
    pr1 is-left-ideal-subset-left-ideal-Semiring

  contains-zero-left-ideal-Semiring :
    is-in-left-ideal-Semiring (zero-Semiring R)
  contains-zero-left-ideal-Semiring =
    pr1 is-additive-submonoid-left-ideal-Semiring

  is-closed-under-add-left-ideal-Semiring :
    {x y : type-Semiring R} → is-in-left-ideal-Semiring x →
    is-in-left-ideal-Semiring y →
    is-in-left-ideal-Semiring (add-Semiring R x y)
  is-closed-under-add-left-ideal-Semiring H K =
    pr2 is-additive-submonoid-left-ideal-Semiring _ _ H K

  is-closed-under-mul-left-ideal-Semiring :
    is-closed-under-mul-left-subset-Semiring R subset-left-ideal-Semiring
  is-closed-under-mul-left-ideal-Semiring =
    pr2 is-left-ideal-subset-left-ideal-Semiring
```

### Right ideals

```agda
module _
  {l1 : Level} (R : Semiring l1)
  where

  is-closed-under-mul-right-subset-Semiring :
    {l2 : Level} → subset-Semiring l2 R → UU (l1 ⊔ l2)
  is-closed-under-mul-right-subset-Semiring P =
    (x : type-Semiring R) (y : type-Semiring R) →
    type-Prop (P x) → type-Prop (P (mul-Semiring R x y))

  is-right-ideal-subset-Semiring :
    {l2 : Level} → subset-Semiring l2 R → UU (l1 ⊔ l2)
  is-right-ideal-subset-Semiring P =
    is-additive-submonoid-Semiring R P ×
    is-closed-under-mul-right-subset-Semiring P

right-ideal-Semiring :
  (l : Level) {l1 : Level} (R : Semiring l1) → UU ((lsuc l) ⊔ l1)
right-ideal-Semiring l R =
  Σ (subset-Semiring l R) (is-right-ideal-subset-Semiring R)

module _
  {l1 l2 : Level} (R : Semiring l1) (I : right-ideal-Semiring l2 R)
  where

  subset-right-ideal-Semiring : subset-Semiring l2 R
  subset-right-ideal-Semiring = pr1 I

  is-in-right-ideal-Semiring : type-Semiring R → UU l2
  is-in-right-ideal-Semiring x = type-Prop (subset-right-ideal-Semiring x)

  type-right-ideal-Semiring : UU (l1 ⊔ l2)
  type-right-ideal-Semiring =
    type-subset-Semiring R subset-right-ideal-Semiring

  inclusion-right-ideal-Semiring : type-right-ideal-Semiring → type-Semiring R
  inclusion-right-ideal-Semiring =
    inclusion-subset-Semiring R subset-right-ideal-Semiring

  is-right-ideal-subset-right-ideal-Semiring :
    is-right-ideal-subset-Semiring R subset-right-ideal-Semiring
  is-right-ideal-subset-right-ideal-Semiring = pr2 I

  is-additive-submonoid-right-ideal-Semiring :
    is-additive-submonoid-Semiring R subset-right-ideal-Semiring
  is-additive-submonoid-right-ideal-Semiring =
    pr1 is-right-ideal-subset-right-ideal-Semiring

  contains-zero-right-ideal-Semiring :
    is-in-right-ideal-Semiring (zero-Semiring R)
  contains-zero-right-ideal-Semiring =
    pr1 is-additive-submonoid-right-ideal-Semiring

  is-closed-under-add-right-ideal-Semiring :
    {x y : type-Semiring R} → is-in-right-ideal-Semiring x →
    is-in-right-ideal-Semiring y →
    is-in-right-ideal-Semiring (add-Semiring R x y)
  is-closed-under-add-right-ideal-Semiring H K =
    pr2 is-additive-submonoid-right-ideal-Semiring _ _ H K

  is-closed-under-mul-right-ideal-Semiring :
    is-closed-under-mul-right-subset-Semiring R subset-right-ideal-Semiring
  is-closed-under-mul-right-ideal-Semiring =
    pr2 is-right-ideal-subset-right-ideal-Semiring
```

### Two-sided ideals

```agda
is-two-sided-ideal-subset-Semiring :
  {l1 l2 : Level} (R : Semiring l1) (P : subset-Semiring l2 R) → UU (l1 ⊔ l2)
is-two-sided-ideal-subset-Semiring R P =
  is-additive-submonoid-Semiring R P ×
  ( is-closed-under-mul-left-subset-Semiring R P ×
    is-closed-under-mul-right-subset-Semiring R P)

two-sided-ideal-Semiring :
  (l : Level) {l1 : Level} (R : Semiring l1) → UU ((lsuc l) ⊔ l1)
two-sided-ideal-Semiring l R =
  Σ (subset-Semiring l R) (is-two-sided-ideal-subset-Semiring R)

module _
  {l1 l2 : Level} (R : Semiring l1) (I : two-sided-ideal-Semiring l2 R)
  where

  subset-two-sided-ideal-Semiring : subset-Semiring l2 R
  subset-two-sided-ideal-Semiring = pr1 I

  is-in-two-sided-ideal-Semiring : type-Semiring R → UU l2
  is-in-two-sided-ideal-Semiring x =
    type-Prop (subset-two-sided-ideal-Semiring x)

  type-two-sided-ideal-Semiring : UU (l1 ⊔ l2)
  type-two-sided-ideal-Semiring =
    type-subset-Semiring R subset-two-sided-ideal-Semiring

  inclusion-two-sided-ideal-Semiring : type-two-sided-ideal-Semiring → type-Semiring R
  inclusion-two-sided-ideal-Semiring =
    inclusion-subset-Semiring R subset-two-sided-ideal-Semiring

  is-two-sided-ideal-subset-two-sided-ideal-Semiring :
    is-two-sided-ideal-subset-Semiring R subset-two-sided-ideal-Semiring
  is-two-sided-ideal-subset-two-sided-ideal-Semiring = pr2 I

  is-additive-submonoid-two-sided-ideal-Semiring :
    is-additive-submonoid-Semiring R subset-two-sided-ideal-Semiring
  is-additive-submonoid-two-sided-ideal-Semiring =
    pr1 is-two-sided-ideal-subset-two-sided-ideal-Semiring

  contains-zero-two-sided-ideal-Semiring :
    is-in-two-sided-ideal-Semiring (zero-Semiring R)
  contains-zero-two-sided-ideal-Semiring =
    pr1 is-additive-submonoid-two-sided-ideal-Semiring

  is-closed-under-add-two-sided-ideal-Semiring :
    {x y : type-Semiring R} → is-in-two-sided-ideal-Semiring x →
    is-in-two-sided-ideal-Semiring y →
    is-in-two-sided-ideal-Semiring (add-Semiring R x y)
  is-closed-under-add-two-sided-ideal-Semiring H K =
    pr2 is-additive-submonoid-two-sided-ideal-Semiring _ _ H K
    
  is-closed-under-mul-left-two-sided-ideal-Semiring :
    is-closed-under-mul-left-subset-Semiring R subset-two-sided-ideal-Semiring
  is-closed-under-mul-left-two-sided-ideal-Semiring =
    pr1 (pr2 is-two-sided-ideal-subset-two-sided-ideal-Semiring)

  is-closed-under-mul-right-two-sided-ideal-Semiring :
    is-closed-under-mul-right-subset-Semiring R subset-two-sided-ideal-Semiring
  is-closed-under-mul-right-two-sided-ideal-Semiring =
    pr2 (pr2 is-two-sided-ideal-subset-two-sided-ideal-Semiring)

  submonoid-two-sided-ideal-Semiring : Submonoid l2 (additive-monoid-Semiring R)
  pr1 submonoid-two-sided-ideal-Semiring =
    subset-two-sided-ideal-Semiring
  pr1 (pr2 submonoid-two-sided-ideal-Semiring) =
    contains-zero-two-sided-ideal-Semiring
  pr2 (pr2 submonoid-two-sided-ideal-Semiring) x y =
    is-closed-under-add-two-sided-ideal-Semiring
```
