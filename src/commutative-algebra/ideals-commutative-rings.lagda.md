# Ideals in commutative rings

```agda
module commutative-algebra.ideals-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings
open import commutative-algebra.subsets-commutative-rings
open import commutative-algebra.subsets-commutative-rings

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels

open import ring-theory.ideals-rings
open import ring-theory.subsets-rings
open import ring-theory.subsets-rings
```

</details>

## Idea

An ideal in a commutative ring is a two-sided ideal in the underlying ring

## Definitions

### Ideals in commutative rings

```agda
module _
  {l1 l2 : Level} (R : Commutative-Ring l1) (S : subset-Commutative-Ring l2 R)
  where

  is-ideal-subset-Commutative-Ring : UU (l1 ⊔ l2)
  is-ideal-subset-Commutative-Ring =
    is-ideal-subset-Ring (ring-Commutative-Ring R) S

ideal-Commutative-Ring :
  {l1 : Level} (l2 : Level) → Commutative-Ring l1 → UU (l1 ⊔ lsuc l2)
ideal-Commutative-Ring l2 R = ideal-Ring l2 (ring-Commutative-Ring R)

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

  ap-inclusion-ideal-Commutative-Ring :
    (x y : type-ideal-Commutative-Ring) → x ＝ y →
    inclusion-ideal-Commutative-Ring x ＝ inclusion-ideal-Commutative-Ring y
  ap-inclusion-ideal-Commutative-Ring =
    ap-inclusion-subset-Commutative-Ring R subset-ideal-Commutative-Ring

  is-in-subset-inclusion-ideal-Commutative-Ring :
    (x : type-ideal-Commutative-Ring) →
    is-in-ideal-Commutative-Ring (inclusion-ideal-Commutative-Ring x)
  is-in-subset-inclusion-ideal-Commutative-Ring =
    is-in-subset-inclusion-subset-Commutative-Ring R
      subset-ideal-Commutative-Ring

  is-closed-under-eq-ideal-Commutative-Ring :
    {x y : type-Commutative-Ring R} → is-in-ideal-Commutative-Ring x →
    (x ＝ y) → is-in-ideal-Commutative-Ring y
  is-closed-under-eq-ideal-Commutative-Ring =
    is-closed-under-eq-subset-Commutative-Ring R subset-ideal-Commutative-Ring

  is-closed-under-eq-ideal-Commutative-Ring' :
    {x y : type-Commutative-Ring R} → is-in-ideal-Commutative-Ring y →
    (x ＝ y) → is-in-ideal-Commutative-Ring x
  is-closed-under-eq-ideal-Commutative-Ring' =
    is-closed-under-eq-subset-Commutative-Ring' R subset-ideal-Commutative-Ring

  is-ideal-subset-ideal-Commutative-Ring :
    is-ideal-subset-Commutative-Ring R subset-ideal-Commutative-Ring
  is-ideal-subset-ideal-Commutative-Ring =
    is-ideal-subset-ideal-Ring
      ( ring-Commutative-Ring R)
      ( I)

  is-additive-subgroup-subset-ideal-Commutative-Ring :
    is-additive-subgroup-subset-Ring
      ( ring-Commutative-Ring R)
      ( subset-ideal-Commutative-Ring)
  is-additive-subgroup-subset-ideal-Commutative-Ring =
    is-additive-subgroup-subset-ideal-Ring
      ( ring-Commutative-Ring R)
      ( I)

  contains-zero-ideal-Commutative-Ring :
    is-in-ideal-Commutative-Ring (zero-Commutative-Ring R)
  contains-zero-ideal-Commutative-Ring =
    contains-zero-ideal-Ring
      ( ring-Commutative-Ring R)
      ( I)

  is-closed-under-addition-ideal-Commutative-Ring :
    {x y : type-Commutative-Ring R} →
    is-in-ideal-Commutative-Ring x → is-in-ideal-Commutative-Ring y →
    is-in-ideal-Commutative-Ring (add-Commutative-Ring R x y)
  is-closed-under-addition-ideal-Commutative-Ring H K =
    pr1 (pr2 is-additive-subgroup-subset-ideal-Commutative-Ring) _ _ H K

  is-closed-under-left-multiplication-ideal-Commutative-Ring :
    is-closed-under-left-multiplication-subset-Commutative-Ring R
      subset-ideal-Commutative-Ring
  is-closed-under-left-multiplication-ideal-Commutative-Ring =
    is-closed-under-left-multiplication-ideal-Ring
      ( ring-Commutative-Ring R)
      ( I)

  is-closed-under-right-multiplication-ideal-Commutative-Ring :
    is-closed-under-right-multiplication-subset-Commutative-Ring R
      subset-ideal-Commutative-Ring
  is-closed-under-right-multiplication-ideal-Commutative-Ring =
    is-closed-under-right-multiplication-ideal-Ring
      ( ring-Commutative-Ring R)
      ( I)

ideal-left-ideal-Commutative-Ring :
  {l1 l2 : Level} (R : Commutative-Ring l1) (S : subset-Commutative-Ring l2 R) →
  contains-zero-subset-Commutative-Ring R S →
  is-closed-under-addition-subset-Commutative-Ring R S →
  is-closed-under-negatives-subset-Commutative-Ring R S →
  is-closed-under-left-multiplication-subset-Commutative-Ring R S →
  ideal-Commutative-Ring l2 R
pr1 (ideal-left-ideal-Commutative-Ring R S z a n m) = S
pr1 (pr1 (pr2 (ideal-left-ideal-Commutative-Ring R S z a n m))) = z
pr1 (pr2 (pr1 (pr2 (ideal-left-ideal-Commutative-Ring R S z a n m)))) = a
pr2 (pr2 (pr1 (pr2 (ideal-left-ideal-Commutative-Ring R S z a n m)))) = n
pr1 (pr2 (pr2 (ideal-left-ideal-Commutative-Ring R S z a n m))) = m
pr2 (pr2 (pr2 (ideal-left-ideal-Commutative-Ring R S z a n m))) x y H =
  is-closed-under-eq-subset-Commutative-Ring R S
    ( m y x H)
    ( commutative-mul-Commutative-Ring R y x)

ideal-right-ideal-Commutative-Ring :
  {l1 l2 : Level} (R : Commutative-Ring l1) (S : subset-Commutative-Ring l2 R) →
  contains-zero-subset-Commutative-Ring R S →
  is-closed-under-addition-subset-Commutative-Ring R S →
  is-closed-under-negatives-subset-Commutative-Ring R S →
  is-closed-under-right-multiplication-subset-Commutative-Ring R S →
  ideal-Commutative-Ring l2 R
pr1 (ideal-right-ideal-Commutative-Ring R S z a n m) = S
pr1 (pr1 (pr2 (ideal-right-ideal-Commutative-Ring R S z a n m))) = z
pr1 (pr2 (pr1 (pr2 (ideal-right-ideal-Commutative-Ring R S z a n m)))) = a
pr2 (pr2 (pr1 (pr2 (ideal-right-ideal-Commutative-Ring R S z a n m)))) = n
pr1 (pr2 (pr2 (ideal-right-ideal-Commutative-Ring R S z a n m))) x y H =
  is-closed-under-eq-subset-Commutative-Ring R S
    ( m y x H)
    ( commutative-mul-Commutative-Ring R y x)
pr2 (pr2 (pr2 (ideal-right-ideal-Commutative-Ring R S z a n m))) = m
```
