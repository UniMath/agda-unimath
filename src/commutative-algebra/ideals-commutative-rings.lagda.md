# Ideals of commutative rings

```agda
module commutative-algebra.ideals-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings
open import commutative-algebra.powers-of-elements-commutative-rings
open import commutative-algebra.subsets-commutative-rings

open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.propositions
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import ring-theory.ideals-rings
open import ring-theory.left-ideals-rings
open import ring-theory.right-ideals-rings
open import ring-theory.subsets-rings
```

</details>

## Idea

An **ideal** in a commutative ring is a two-sided ideal in the underlying ring.

## Definitions

### Ideals in commutative rings

```agda
module _
  {l1 l2 : Level} (R : Commutative-Ring l1) (S : subset-Commutative-Ring l2 R)
  where

  is-ideal-subset-Commutative-Ring : UU (l1 ⊔ l2)
  is-ideal-subset-Commutative-Ring =
    is-ideal-subset-Ring (ring-Commutative-Ring R) S

  is-left-ideal-subset-Commutative-Ring : UU (l1 ⊔ l2)
  is-left-ideal-subset-Commutative-Ring =
    is-left-ideal-subset-Ring (ring-Commutative-Ring R) S

  is-right-ideal-subset-Commutative-Ring : UU (l1 ⊔ l2)
  is-right-ideal-subset-Commutative-Ring =
    is-right-ideal-subset-Ring (ring-Commutative-Ring R) S

ideal-Commutative-Ring :
  {l1 : Level} (l2 : Level) → Commutative-Ring l1 → UU (l1 ⊔ lsuc l2)
ideal-Commutative-Ring l2 R = ideal-Ring l2 (ring-Commutative-Ring R)

left-ideal-Commutative-Ring :
  {l1 : Level} (l2 : Level) → Commutative-Ring l1 → UU (l1 ⊔ lsuc l2)
left-ideal-Commutative-Ring l2 R =
  left-ideal-Ring l2 (ring-Commutative-Ring R)

right-ideal-Commutative-Ring :
  {l1 : Level} (l2 : Level) → Commutative-Ring l1 → UU (l1 ⊔ lsuc l2)
right-ideal-Commutative-Ring l2 R =
  right-ideal-Ring l2 (ring-Commutative-Ring R)

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

  is-ideal-ideal-Commutative-Ring :
    is-ideal-subset-Commutative-Ring R subset-ideal-Commutative-Ring
  is-ideal-ideal-Commutative-Ring =
    is-ideal-ideal-Ring (ring-Commutative-Ring R) I

  is-additive-subgroup-ideal-Commutative-Ring :
    is-additive-subgroup-subset-Ring
      ( ring-Commutative-Ring R)
      ( subset-ideal-Commutative-Ring)
  is-additive-subgroup-ideal-Commutative-Ring =
    is-additive-subgroup-ideal-Ring (ring-Commutative-Ring R) I

  contains-zero-ideal-Commutative-Ring :
    contains-zero-subset-Commutative-Ring R subset-ideal-Commutative-Ring
  contains-zero-ideal-Commutative-Ring =
    contains-zero-ideal-Ring (ring-Commutative-Ring R) I

  is-closed-under-addition-ideal-Commutative-Ring :
    is-closed-under-addition-subset-Commutative-Ring R
      subset-ideal-Commutative-Ring
  is-closed-under-addition-ideal-Commutative-Ring =
    is-closed-under-addition-ideal-Ring (ring-Commutative-Ring R) I

  is-closed-under-negatives-ideal-Commutative-Ring :
    {x : type-Commutative-Ring R} →
    is-in-ideal-Commutative-Ring x →
    is-in-ideal-Commutative-Ring (neg-Commutative-Ring R x)
  is-closed-under-negatives-ideal-Commutative-Ring =
    pr2 (pr2 is-additive-subgroup-ideal-Commutative-Ring)

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

  is-closed-under-powers-ideal-Commutative-Ring :
    (n : ℕ) (x : type-Commutative-Ring R) →
    is-in-ideal-Commutative-Ring x →
    is-in-ideal-Commutative-Ring (power-Commutative-Ring R (succ-ℕ n) x)
  is-closed-under-powers-ideal-Commutative-Ring zero-ℕ x H = H
  is-closed-under-powers-ideal-Commutative-Ring (succ-ℕ n) x H =
    is-closed-under-left-multiplication-ideal-Commutative-Ring
      ( power-Commutative-Ring R (succ-ℕ n) x)
      ( x)
      ( H)

  left-ideal-ideal-Commutative-Ring : left-ideal-Commutative-Ring l2 R
  left-ideal-ideal-Commutative-Ring =
    left-ideal-ideal-Ring (ring-Commutative-Ring R) I

  right-ideal-ideal-Commutative-Ring : right-ideal-Commutative-Ring l2 R
  right-ideal-ideal-Commutative-Ring =
    right-ideal-ideal-Ring (ring-Commutative-Ring R) I

ideal-left-ideal-Commutative-Ring :
  {l1 l2 : Level}
  (R : Commutative-Ring l1) (S : subset-Commutative-Ring l2 R) →
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
  {l1 l2 : Level}
  (R : Commutative-Ring l1) (S : subset-Commutative-Ring l2 R) →
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

## Properties

### Characterizing equality of ideals in commutative rings

```agda
module _
  {l1 l2 l3 : Level}
  (R : Commutative-Ring l1) (I : ideal-Commutative-Ring l2 R)
  where

  has-same-elements-ideal-Commutative-Ring :
    (J : ideal-Commutative-Ring l3 R) → UU (l1 ⊔ l2 ⊔ l3)
  has-same-elements-ideal-Commutative-Ring =
    has-same-elements-ideal-Ring (ring-Commutative-Ring R) I

module _
  {l1 l2 : Level} (R : Commutative-Ring l1) (I : ideal-Commutative-Ring l2 R)
  where

  refl-has-same-elements-ideal-Commutative-Ring :
    has-same-elements-ideal-Commutative-Ring R I I
  refl-has-same-elements-ideal-Commutative-Ring =
    refl-has-same-elements-ideal-Ring (ring-Commutative-Ring R) I

  is-torsorial-has-same-elements-ideal-Commutative-Ring :
    is-torsorial (has-same-elements-ideal-Commutative-Ring R I)
  is-torsorial-has-same-elements-ideal-Commutative-Ring =
    is-torsorial-has-same-elements-ideal-Ring (ring-Commutative-Ring R) I

  has-same-elements-eq-ideal-Commutative-Ring :
    (J : ideal-Commutative-Ring l2 R) →
    (I ＝ J) → has-same-elements-ideal-Commutative-Ring R I J
  has-same-elements-eq-ideal-Commutative-Ring =
    has-same-elements-eq-ideal-Ring (ring-Commutative-Ring R) I

  is-equiv-has-same-elements-eq-ideal-Commutative-Ring :
    (J : ideal-Commutative-Ring l2 R) →
    is-equiv (has-same-elements-eq-ideal-Commutative-Ring J)
  is-equiv-has-same-elements-eq-ideal-Commutative-Ring =
    is-equiv-has-same-elements-eq-ideal-Ring (ring-Commutative-Ring R) I

  extensionality-ideal-Commutative-Ring :
    (J : ideal-Commutative-Ring l2 R) →
    (I ＝ J) ≃ has-same-elements-ideal-Commutative-Ring R I J
  extensionality-ideal-Commutative-Ring =
    extensionality-ideal-Ring (ring-Commutative-Ring R) I

  eq-has-same-elements-ideal-Commutative-Ring :
    (J : ideal-Commutative-Ring l2 R) →
    has-same-elements-ideal-Commutative-Ring R I J → I ＝ J
  eq-has-same-elements-ideal-Commutative-Ring =
    eq-has-same-elements-ideal-Ring (ring-Commutative-Ring R) I
```
