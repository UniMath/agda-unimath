# Ideals in commutative semirings

```agda
module commutative-algebra.ideals-commutative-semirings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-semirings
open import commutative-algebra.subsets-commutative-semirings

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import ring-theory.ideals-semirings
open import ring-theory.subsets-semirings
```

</details>

## Idea

An ideal in a commutative semiring is a two-sided ideal in the underlying
semiring

## Definitions

### Ideals in commutative rings

```agda
module _
  {l1 l2 : Level} (R : Commutative-Semiring l1)
  (S : subset-Commutative-Semiring l2 R)
  where

  is-closed-under-add-subset-Commutative-Semiring : UU (l1 ⊔ l2)
  is-closed-under-add-subset-Commutative-Semiring =
    (x y : type-Commutative-Semiring R) →
    is-in-subset-Commutative-Semiring R S x →
    is-in-subset-Commutative-Semiring R S y →
    is-in-subset-Commutative-Semiring R S (add-Commutative-Semiring R x y)

  is-closed-under-mul-left-subset-Commutative-Semiring : UU (l1 ⊔ l2)
  is-closed-under-mul-left-subset-Commutative-Semiring =
    is-closed-under-mul-left-subset-Semiring (semiring-Commutative-Semiring R) S

  is-closed-under-mul-right-subset-Commutative-Semiring : UU (l1 ⊔ l2)
  is-closed-under-mul-right-subset-Commutative-Semiring =
    is-closed-under-mul-right-subset-Semiring
      ( semiring-Commutative-Semiring R)
      ( S)

  is-ideal-subset-Commutative-Semiring : UU (l1 ⊔ l2)
  is-ideal-subset-Commutative-Semiring =
    is-two-sided-ideal-subset-Semiring (semiring-Commutative-Semiring R) S

ideal-Commutative-Semiring :
  {l1 : Level} (l2 : Level) → Commutative-Semiring l1 → UU (l1 ⊔ lsuc l2)
ideal-Commutative-Semiring l2 R =
  two-sided-ideal-Semiring l2 (semiring-Commutative-Semiring R)

module _
  {l1 l2 : Level} (R : Commutative-Semiring l1)
  (I : ideal-Commutative-Semiring l2 R)
  where

  subset-ideal-Commutative-Semiring : subset-Commutative-Semiring l2 R
  subset-ideal-Commutative-Semiring = pr1 I

  is-in-ideal-Commutative-Semiring : type-Commutative-Semiring R → UU l2
  is-in-ideal-Commutative-Semiring x =
    type-Prop (subset-ideal-Commutative-Semiring x)

  type-ideal-Commutative-Semiring : UU (l1 ⊔ l2)
  type-ideal-Commutative-Semiring =
    type-subset-Commutative-Semiring R subset-ideal-Commutative-Semiring

  inclusion-ideal-Commutative-Semiring :
    type-ideal-Commutative-Semiring → type-Commutative-Semiring R
  inclusion-ideal-Commutative-Semiring =
    inclusion-subset-Commutative-Semiring R subset-ideal-Commutative-Semiring

  is-ideal-subset-ideal-Commutative-Semiring :
    is-ideal-subset-Commutative-Semiring R subset-ideal-Commutative-Semiring
  is-ideal-subset-ideal-Commutative-Semiring =
    is-two-sided-ideal-subset-two-sided-ideal-Semiring
      ( semiring-Commutative-Semiring R)
      ( I)

  is-additive-submonoid-ideal-Commutative-Semiring :
    is-additive-submonoid-Semiring
      ( semiring-Commutative-Semiring R)
      ( subset-ideal-Commutative-Semiring)
  is-additive-submonoid-ideal-Commutative-Semiring =
    is-additive-submonoid-two-sided-ideal-Semiring
      ( semiring-Commutative-Semiring R)
      ( I)

  contains-zero-ideal-Commutative-Semiring :
    is-in-ideal-Commutative-Semiring (zero-Commutative-Semiring R)
  contains-zero-ideal-Commutative-Semiring =
    contains-zero-two-sided-ideal-Semiring
      ( semiring-Commutative-Semiring R)
      ( I)

  is-closed-under-add-ideal-Commutative-Semiring :
    {x y : type-Commutative-Semiring R} →
    is-in-ideal-Commutative-Semiring x → is-in-ideal-Commutative-Semiring y →
    is-in-ideal-Commutative-Semiring (add-Commutative-Semiring R x y)
  is-closed-under-add-ideal-Commutative-Semiring H K =
    pr2 is-additive-submonoid-ideal-Commutative-Semiring _ _ H K

  is-closed-under-mul-left-ideal-Commutative-Semiring :
    is-closed-under-mul-left-subset-Commutative-Semiring R
      subset-ideal-Commutative-Semiring
  is-closed-under-mul-left-ideal-Commutative-Semiring =
    is-closed-under-mul-left-two-sided-ideal-Semiring
      ( semiring-Commutative-Semiring R)
      ( I)

  is-closed-under-mul-right-ideal-Commutative-Semiring :
    is-closed-under-mul-right-subset-Commutative-Semiring R
      subset-ideal-Commutative-Semiring
  is-closed-under-mul-right-ideal-Commutative-Semiring =
    is-closed-under-mul-right-two-sided-ideal-Semiring
      ( semiring-Commutative-Semiring R)
      ( I)

ideal-left-ideal-Commutative-Semiring :
  {l1 l2 : Level} (R : Commutative-Semiring l1)
  (S : subset-Commutative-Semiring l2 R) →
  contains-zero-subset-Commutative-Semiring R S →
  is-closed-under-add-subset-Commutative-Semiring R S →
  is-closed-under-mul-left-subset-Commutative-Semiring R S →
  ideal-Commutative-Semiring l2 R
pr1 (ideal-left-ideal-Commutative-Semiring R S z a m) = S
pr1 (pr1 (pr2 (ideal-left-ideal-Commutative-Semiring R S z a m))) = z
pr2 (pr1 (pr2 (ideal-left-ideal-Commutative-Semiring R S z a m))) = a
pr1 (pr2 (pr2 (ideal-left-ideal-Commutative-Semiring R S z a m))) = m
pr2 (pr2 (pr2 (ideal-left-ideal-Commutative-Semiring R S z a m))) x y H =
  is-closed-under-eq-subset-Commutative-Semiring R S
    ( m y x H)
    ( commutative-mul-Commutative-Semiring R y x)

ideal-right-ideal-Commutative-Semiring :
  {l1 l2 : Level} (R : Commutative-Semiring l1)
  (S : subset-Commutative-Semiring l2 R) →
  contains-zero-subset-Commutative-Semiring R S →
  is-closed-under-add-subset-Commutative-Semiring R S →
  is-closed-under-mul-right-subset-Commutative-Semiring R S →
  ideal-Commutative-Semiring l2 R
pr1 (ideal-right-ideal-Commutative-Semiring R S z a m) = S
pr1 (pr1 (pr2 (ideal-right-ideal-Commutative-Semiring R S z a m))) = z
pr2 (pr1 (pr2 (ideal-right-ideal-Commutative-Semiring R S z a m))) = a
pr1 (pr2 (pr2 (ideal-right-ideal-Commutative-Semiring R S z a m))) x y H =
  is-closed-under-eq-subset-Commutative-Semiring R S
    ( m y x H)
    ( commutative-mul-Commutative-Semiring R y x)
pr2 (pr2 (pr2 (ideal-right-ideal-Commutative-Semiring R S z a m))) = m
```
