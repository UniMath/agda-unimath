# Ideals in commutative rings

```agda
module commutative-algebra.ideals-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import ring-theory.ideals-rings
```

</details>

## Idea

An ideal in a commutative ring is a two-sided ideal in the underlying ring

## Definitions

### Subsets of commutative rings

```agda
subset-Commutative-Ring :
  {l1 : Level} (l2 : Level) → Commutative-Ring l1 → UU (l1 ⊔ lsuc l2)
subset-Commutative-Ring l2 R = subtype l2 (type-Commutative-Ring R)

module _
  {l1 l2 : Level} (R : Commutative-Ring l1) (S : subset-Commutative-Ring l2 R)
  where

  is-in-subset-Commutative-Ring : type-Commutative-Ring R → UU l2
  is-in-subset-Commutative-Ring = is-in-subtype S

  is-prop-is-in-subset-Commutative-Ring :
    (x : type-Commutative-Ring R) → is-prop (is-in-subset-Commutative-Ring x)
  is-prop-is-in-subset-Commutative-Ring =
    is-prop-is-in-subtype S

  type-subset-Commutative-Ring : UU (l1 ⊔ l2)
  type-subset-Commutative-Ring = type-subtype S

  inclusion-subset-Commutative-Ring :
    type-subset-Commutative-Ring → type-Commutative-Ring R
  inclusion-subset-Commutative-Ring = inclusion-subtype S

  is-in-subset-inclusion-subset-Commutative-Ring :
    (x : type-subset-Commutative-Ring) →
    is-in-subset-Commutative-Ring (inclusion-subset-Commutative-Ring x)
  is-in-subset-inclusion-subset-Commutative-Ring =
    is-in-subtype-inclusion-subtype S
```

### Ideals in commutative rings

```agda
module _
  {l1 l2 : Level} (R : Commutative-Ring l1) (S : subset-Commutative-Ring l2 R)
  where

  is-closed-under-mul-left-subset-Commutative-Ring : UU (l1 ⊔ l2)
  is-closed-under-mul-left-subset-Commutative-Ring =
    is-closed-under-mul-left-subset-Ring (ring-Commutative-Ring R) S

  is-closed-under-mul-right-subset-Commutative-Ring : UU (l1 ⊔ l2)
  is-closed-under-mul-right-subset-Commutative-Ring =
    is-closed-under-mul-right-subset-Ring (ring-Commutative-Ring R) S

  is-ideal-subset-Commutative-Ring : UU (l1 ⊔ l2)
  is-ideal-subset-Commutative-Ring =
    is-two-sided-ideal-subset-Ring (ring-Commutative-Ring R) S

ideal-Commutative-Ring :
  {l1 : Level} (l2 : Level) → Commutative-Ring l1 → UU (l1 ⊔ lsuc l2)
ideal-Commutative-Ring l2 R = two-sided-ideal-Ring l2 (ring-Commutative-Ring R)

module _
  {l1 l2 : Level} (R : Commutative-Ring l1) (I : ideal-Commutative-Ring l2 R)
  where

  subset-ideal-Commutative-Ring : subset-Commutative-Ring l2 R
  subset-ideal-Commutative-Ring = pr1 I

  is-in-ideal-Commutative-Ring : type-Commutative-Ring R → UU l2
  is-in-ideal-Commutative-Ring x = type-Prop (subset-ideal-Commutative-Ring x)

  type-ideal-Commutative-Ring : UU (l1 ⊔ l2)
  type-ideal-Commutative-Ring =
    type-subset-Commutative-Ring R subset-ideal-Commutative-Ring

  inclusion-ideal-Commutative-Ring :
    type-ideal-Commutative-Ring → type-Commutative-Ring R
  inclusion-ideal-Commutative-Ring =
    inclusion-subset-Commutative-Ring R subset-ideal-Commutative-Ring

  is-ideal-subset-ideal-Commutative-Ring :
    is-ideal-subset-Commutative-Ring R subset-ideal-Commutative-Ring
  is-ideal-subset-ideal-Commutative-Ring =
    is-two-sided-ideal-subset-two-sided-ideal-Ring
      ( ring-Commutative-Ring R)
      ( I)

  is-additive-subgroup-subset-ideal-Commutative-Ring :
    is-additive-subgroup-subset-Ring
      ( ring-Commutative-Ring R)
      ( subset-ideal-Commutative-Ring)
  is-additive-subgroup-subset-ideal-Commutative-Ring =
    is-additive-subgroup-subset-two-sided-ideal-Ring
      ( ring-Commutative-Ring R)
      ( I)

  contains-zero-ideal-Commutative-Ring :
    is-in-ideal-Commutative-Ring (zero-Commutative-Ring R)
  contains-zero-ideal-Commutative-Ring =
    contains-zero-two-sided-ideal-Ring
      ( ring-Commutative-Ring R)
      ( I)

  is-closed-under-add-ideal-Commutative-Ring :
    {x y : type-Commutative-Ring R} →
    is-in-ideal-Commutative-Ring x → is-in-ideal-Commutative-Ring y →
    is-in-ideal-Commutative-Ring (add-Commutative-Ring R x y)
  is-closed-under-add-ideal-Commutative-Ring H K =
    pr1 (pr2 is-additive-subgroup-subset-ideal-Commutative-Ring) _ _ H K

  is-closed-under-mul-left-ideal-Commutative-Ring :
    is-closed-under-mul-left-subset-Commutative-Ring R
      subset-ideal-Commutative-Ring
  is-closed-under-mul-left-ideal-Commutative-Ring =
    is-closed-under-mul-left-two-sided-ideal-Ring
      ( ring-Commutative-Ring R)
      ( I)

  is-closed-under-mul-right-ideal-Commutative-Ring :
    is-closed-under-mul-right-subset-Commutative-Ring R
      subset-ideal-Commutative-Ring
  is-closed-under-mul-right-ideal-Commutative-Ring =
    is-closed-under-mul-right-two-sided-ideal-Ring
      ( ring-Commutative-Ring R)
      ( I)
```
