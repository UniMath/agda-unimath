# Ideals of commutative semirings

```agda
module commutative-algebra.ideals-commutative-semirings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-semirings
open import commutative-algebra.subsets-commutative-semirings

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import ring-theory.ideals-semirings
open import ring-theory.left-ideals-semirings
open import ring-theory.right-ideals-semirings
open import ring-theory.subsets-semirings
```

</details>

## Idea

An {{#concept "ideal" Disambiguation="commutative semiring" Agda=ideal-Commutative-Semiring}} in a [commutative semiring](commutative-algebra.commutative-semirings.md) is a [left ideal](ring-theory.left-ideals-semirings.md) in the underlying [semiring](ring-theory.semirings.md). By virtue of commutativity, any ideal in a commutative semiring is also a [right idea](ring-theory.right-ideals-semirings.md) and a [two-sided ideal](ring-theory.ideals-semirings.md) in the underlying semiring.

## Definitions

### Left, right, and two-sided ideals

```agda
module _
  {l1 l2 : Level} (A : Commutative-Semiring l1)
  (S : subset-Commutative-Semiring l2 A)
  where

  is-left-ideal-subset-Commutative-Semiring : UU (l1 ⊔ l2)
  is-left-ideal-subset-Commutative-Semiring =
    is-left-ideal-subset-Semiring (semiring-Commutative-Semiring A) S

  is-prop-is-left-ideal-subset-Commutative-Semiring :
    is-prop is-left-ideal-subset-Commutative-Semiring
  is-prop-is-left-ideal-subset-Commutative-Semiring =
    is-prop-is-left-ideal-subset-Semiring (semiring-Commutative-Semiring A) S

  is-left-ideal-prop-subset-Commutative-Semiring :
    Prop (l1 ⊔ l2)
  is-left-ideal-prop-subset-Commutative-Semiring =
    is-left-ideal-prop-subset-Semiring (semiring-Commutative-Semiring A) S

  is-right-ideal-subset-Commutative-Semiring : UU (l1 ⊔ l2)
  is-right-ideal-subset-Commutative-Semiring =
    is-right-ideal-subset-Semiring (semiring-Commutative-Semiring A) S

  is-prop-is-right-ideal-subset-Commutative-Semiring :
    is-prop is-right-ideal-subset-Commutative-Semiring
  is-prop-is-right-ideal-subset-Commutative-Semiring =
    is-prop-is-right-ideal-subset-Semiring (semiring-Commutative-Semiring A) S

  is-right-ideal-prop-subset-Commutative-Semiring :
    Prop (l1 ⊔ l2)
  is-right-ideal-prop-subset-Commutative-Semiring =
    is-right-ideal-prop-subset-Semiring (semiring-Commutative-Semiring A) S

  is-two-sided-ideal-subset-Commutative-Semiring : UU (l1 ⊔ l2)
  is-two-sided-ideal-subset-Commutative-Semiring =
    is-ideal-subset-Semiring (semiring-Commutative-Semiring A) S

  is-prop-is-two-sided-ideal-subset-Commutative-Semiring :
    is-prop is-two-sided-ideal-subset-Commutative-Semiring
  is-prop-is-two-sided-ideal-subset-Commutative-Semiring =
    is-prop-is-ideal-subset-Semiring (semiring-Commutative-Semiring A) S

  is-two-sided-ideal-prop-subset-Commutative-Semiring :
    Prop (l1 ⊔ l2)
  is-two-sided-ideal-prop-subset-Commutative-Semiring =
    is-ideal-prop-subset-Semiring (semiring-Commutative-Semiring A) S

  is-ideal-subset-Commutative-Semiring :
    UU (l1 ⊔ l2)
  is-ideal-subset-Commutative-Semiring =
    is-two-sided-ideal-subset-Commutative-Semiring

  is-prop-is-ideal-subset-Commutative-Semiring :
    is-prop is-ideal-subset-Commutative-Semiring
  is-prop-is-ideal-subset-Commutative-Semiring =
    is-prop-is-two-sided-ideal-subset-Commutative-Semiring

  is-ideal-prop-subset-Commutative-Semiring :
    Prop (l1 ⊔ l2)
  is-ideal-prop-subset-Commutative-Semiring =
    is-two-sided-ideal-prop-subset-Commutative-Semiring

  is-left-ideal-is-right-ideal-subset-Commutative-Semiring :
    is-right-ideal-subset-Commutative-Semiring →
    is-left-ideal-subset-Commutative-Semiring
  pr1 (is-left-ideal-is-right-ideal-subset-Commutative-Semiring (H , K)) =
    H
  pr2 (is-left-ideal-is-right-ideal-subset-Commutative-Semiring (H , K)) U =
    is-closed-under-eq-subset-Commutative-Semiring A S
      ( K U)
      ( commutative-mul-Commutative-Semiring A _ _)

  is-right-ideal-is-left-ideal-subset-Commutative-Semiring :
    is-left-ideal-subset-Commutative-Semiring →
    is-right-ideal-subset-Commutative-Semiring
  pr1 (is-right-ideal-is-left-ideal-subset-Commutative-Semiring (H , K)) =
    H
  pr2 (is-right-ideal-is-left-ideal-subset-Commutative-Semiring (H , K)) U =
    is-closed-under-eq-subset-Commutative-Semiring A S
      ( K U)
      ( commutative-mul-Commutative-Semiring A _ _)

  is-left-ideal-is-two-sided-ideal-subset-Commutative-Semiring :
    is-two-sided-ideal-subset-Commutative-Semiring →
    is-left-ideal-subset-Commutative-Semiring
  pr1 (is-left-ideal-is-two-sided-ideal-subset-Commutative-Semiring (H , K)) =
    H
  pr2 (is-left-ideal-is-two-sided-ideal-subset-Commutative-Semiring (H , K)) U =
    is-closed-under-eq-subset-Commutative-Semiring A S
      ( K U)
      ( right-unit-law-mul-Commutative-Semiring A _)

  is-two-sided-ideal-is-left-ideal-subset-Commutative-Semiring :
    is-left-ideal-subset-Commutative-Semiring →
    is-two-sided-ideal-subset-Commutative-Semiring
  pr1 (is-two-sided-ideal-is-left-ideal-subset-Commutative-Semiring (H , K)) =
    H
  pr2 (is-two-sided-ideal-is-left-ideal-subset-Commutative-Semiring (H , K)) U =
    is-closed-under-eq-subset-Commutative-Semiring A S
      ( K (K U))
      ( commutative-mul-Commutative-Semiring A _ _)

  is-two-sided-ideal-is-right-ideal-subset-Commutative-Semiring :
    is-right-ideal-subset-Commutative-Semiring →
    is-two-sided-ideal-subset-Commutative-Semiring
  pr1 (is-two-sided-ideal-is-right-ideal-subset-Commutative-Semiring (H , K)) =
    H
  pr2
    ( is-two-sided-ideal-is-right-ideal-subset-Commutative-Semiring (H , K)) U =
    is-closed-under-eq-subset-Commutative-Semiring A S
      ( K (K U))
      ( ap
        ( mul-Commutative-Semiring' A _)
        ( commutative-mul-Commutative-Semiring A _ _))

  is-right-ideal-is-two-sided-ideal-subset-Commutative-Semiring :
    is-two-sided-ideal-subset-Commutative-Semiring →
    is-right-ideal-subset-Commutative-Semiring
  pr1 (is-right-ideal-is-two-sided-ideal-subset-Commutative-Semiring (H , K)) =
    H
  pr2
    ( is-right-ideal-is-two-sided-ideal-subset-Commutative-Semiring (H , K)) U =
    is-closed-under-eq-subset-Commutative-Semiring A S
      ( K U)
      ( ap
        ( mul-Commutative-Semiring' A _)
        ( left-unit-law-mul-Commutative-Semiring A _))

  is-ideal-is-left-ideal-subset-Commutative-Semiring :
    is-left-ideal-subset-Commutative-Semiring →
    is-ideal-subset-Commutative-Semiring
  is-ideal-is-left-ideal-subset-Commutative-Semiring =
    is-two-sided-ideal-is-left-ideal-subset-Commutative-Semiring

  is-left-ideal-is-ideal-subset-Commutative-Semiring :
    is-ideal-subset-Commutative-Semiring →
    is-left-ideal-subset-Commutative-Semiring
  is-left-ideal-is-ideal-subset-Commutative-Semiring =
    is-left-ideal-is-two-sided-ideal-subset-Commutative-Semiring

  is-ideal-is-right-ideal-subset-Commutative-Semiring :
    is-right-ideal-subset-Commutative-Semiring →
    is-ideal-subset-Commutative-Semiring
  is-ideal-is-right-ideal-subset-Commutative-Semiring =
    is-two-sided-ideal-is-right-ideal-subset-Commutative-Semiring

  is-right-ideal-is-ideal-subset-Commutative-Semiring :
    is-ideal-subset-Commutative-Semiring →
    is-right-ideal-subset-Commutative-Semiring
  is-right-ideal-is-ideal-subset-Commutative-Semiring =
    is-right-ideal-is-two-sided-ideal-subset-Commutative-Semiring

  is-ideal-is-two-sided-ideal-subset-Commutative-Semiring :
    is-two-sided-ideal-subset-Commutative-Semiring →
    is-ideal-subset-Commutative-Semiring
  is-ideal-is-two-sided-ideal-subset-Commutative-Semiring =
    id

  is-two-sided-ideal-is-ideal-subset-Commutative-Semiring :
    is-ideal-subset-Commutative-Semiring →
    is-two-sided-ideal-subset-Commutative-Semiring
  is-two-sided-ideal-is-ideal-subset-Commutative-Semiring =
    id
```

### Ideals in commutative semirings

```agda
module _
  {l1 : Level} (l2 : Level) (A : Commutative-Semiring l1)
  where
  
  ideal-Commutative-Semiring :
    UU (l1 ⊔ lsuc l2)
  ideal-Commutative-Semiring =
    ideal-Semiring l2 (semiring-Commutative-Semiring A)

  left-ideal-Commutative-Semiring :
    UU (l1 ⊔ lsuc l2)
  left-ideal-Commutative-Semiring =
    left-ideal-Semiring l2 (semiring-Commutative-Semiring A)

  right-ideal-Commutative-Semiring :
    UU (l1 ⊔ lsuc l2)
  right-ideal-Commutative-Semiring =
    right-ideal-Semiring l2 (semiring-Commutative-Semiring A)

  two-sided-ideal-Commutative-Semiring :
    UU (l1 ⊔ lsuc l2)
  two-sided-ideal-Commutative-Semiring =
    ideal-Semiring l2 (semiring-Commutative-Semiring A)

module _
  {l1 l2 : Level} (A : Commutative-Semiring l1)
  (I : ideal-Commutative-Semiring l2 A)
  where

  subset-ideal-Commutative-Semiring : subset-Commutative-Semiring l2 A
  subset-ideal-Commutative-Semiring =
    subset-ideal-Semiring (semiring-Commutative-Semiring A) I

  is-ideal-ideal-Commutative-Semiring :
    is-ideal-subset-Commutative-Semiring A subset-ideal-Commutative-Semiring
  is-ideal-ideal-Commutative-Semiring =
    is-ideal-ideal-Semiring (semiring-Commutative-Semiring A) I

  is-left-ideal-ideal-Commutative-Semiring :
    is-left-ideal-subset-Commutative-Semiring A
      subset-ideal-Commutative-Semiring
  is-left-ideal-ideal-Commutative-Semiring =
    is-left-ideal-is-ideal-subset-Commutative-Semiring A
      subset-ideal-Commutative-Semiring
      is-ideal-ideal-Commutative-Semiring

  left-ideal-ideal-Commutative-Semiring :
    left-ideal-Commutative-Semiring l2 A
  pr1 left-ideal-ideal-Commutative-Semiring =
    subset-ideal-Commutative-Semiring
  pr2 left-ideal-ideal-Commutative-Semiring =
    is-left-ideal-ideal-Commutative-Semiring

  is-right-ideal-ideal-Commutative-Semiring :
    is-right-ideal-subset-Commutative-Semiring A
      subset-ideal-Commutative-Semiring
  is-right-ideal-ideal-Commutative-Semiring =
    is-right-ideal-is-ideal-subset-Commutative-Semiring A
      subset-ideal-Commutative-Semiring
      is-ideal-ideal-Commutative-Semiring

  right-ideal-ideal-Commutative-Semiring :
    right-ideal-Commutative-Semiring l2 A
  pr1 right-ideal-ideal-Commutative-Semiring =
    subset-ideal-Commutative-Semiring
  pr2 right-ideal-ideal-Commutative-Semiring =
    is-right-ideal-ideal-Commutative-Semiring

  is-two-sided-ideal-ideal-Commutative-Semiring :
    is-two-sided-ideal-subset-Commutative-Semiring A
      subset-ideal-Commutative-Semiring
  is-two-sided-ideal-ideal-Commutative-Semiring =
    is-two-sided-ideal-is-ideal-subset-Commutative-Semiring A
      subset-ideal-Commutative-Semiring
      is-ideal-ideal-Commutative-Semiring

  two-sided-ideal-ideal-Commutative-Semiring :
    two-sided-ideal-Commutative-Semiring l2 A
  pr1 two-sided-ideal-ideal-Commutative-Semiring =
    subset-ideal-Commutative-Semiring
  pr2 two-sided-ideal-ideal-Commutative-Semiring =
    is-two-sided-ideal-ideal-Commutative-Semiring

  is-in-ideal-Commutative-Semiring : type-Commutative-Semiring A → UU l2
  is-in-ideal-Commutative-Semiring =
    is-in-ideal-Semiring (semiring-Commutative-Semiring A) I

  is-prop-is-in-ideal-Commutative-Semiring :
    (x : type-Commutative-Semiring A) →
    is-prop (is-in-ideal-Commutative-Semiring x)
  is-prop-is-in-ideal-Commutative-Semiring =
    is-prop-is-in-ideal-Semiring (semiring-Commutative-Semiring A) I

  type-ideal-Commutative-Semiring : UU (l1 ⊔ l2)
  type-ideal-Commutative-Semiring =
    type-ideal-Semiring (semiring-Commutative-Semiring A) I

  inclusion-ideal-Commutative-Semiring :
    type-ideal-Commutative-Semiring → type-Commutative-Semiring A
  inclusion-ideal-Commutative-Semiring =
    inclusion-ideal-Semiring (semiring-Commutative-Semiring A) I

  ap-inclusion-ideal-Commutative-Semiring :
    (x y : type-ideal-Commutative-Semiring) → x ＝ y →
    inclusion-ideal-Commutative-Semiring x ＝
    inclusion-ideal-Commutative-Semiring y
  ap-inclusion-ideal-Commutative-Semiring =
    ap-inclusion-ideal-Semiring (semiring-Commutative-Semiring A) I

  is-in-subset-inclusion-ideal-Commutative-Semiring :
    (x : type-ideal-Commutative-Semiring) →
    is-in-ideal-Commutative-Semiring (inclusion-ideal-Commutative-Semiring x)
  is-in-subset-inclusion-ideal-Commutative-Semiring =
    is-in-subset-inclusion-ideal-Semiring
      ( semiring-Commutative-Semiring A)
      ( I)

  is-closed-under-eq-ideal-Commutative-Semiring :
    {x y : type-Commutative-Semiring A} → is-in-ideal-Commutative-Semiring x →
    (x ＝ y) → is-in-ideal-Commutative-Semiring y
  is-closed-under-eq-ideal-Commutative-Semiring =
    is-closed-under-eq-ideal-Semiring (semiring-Commutative-Semiring A) I

  is-closed-under-eq-ideal-Commutative-Semiring' :
    {x y : type-Commutative-Semiring A} → is-in-ideal-Commutative-Semiring y →
    (x ＝ y) → is-in-ideal-Commutative-Semiring x
  is-closed-under-eq-ideal-Commutative-Semiring' =
    is-closed-under-eq-ideal-Semiring' (semiring-Commutative-Semiring A) I

  is-additive-submonoid-ideal-Commutative-Semiring :
    is-additive-submonoid-subset-Semiring
      ( semiring-Commutative-Semiring A)
      ( subset-ideal-Commutative-Semiring)
  is-additive-submonoid-ideal-Commutative-Semiring =
    is-additive-submonoid-ideal-Semiring
      ( semiring-Commutative-Semiring A)
      ( I)

  contains-zero-ideal-Commutative-Semiring :
    contains-zero-subset-Commutative-Semiring A
      subset-ideal-Commutative-Semiring
  contains-zero-ideal-Commutative-Semiring =
    contains-zero-ideal-Semiring (semiring-Commutative-Semiring A) I

  is-closed-under-addition-ideal-Commutative-Semiring :
    is-closed-under-addition-subset-Commutative-Semiring A
      subset-ideal-Commutative-Semiring
  is-closed-under-addition-ideal-Commutative-Semiring =
    is-closed-under-addition-ideal-Semiring
      ( semiring-Commutative-Semiring A)
      ( I)

  is-closed-under-left-multiplication-ideal-Commutative-Semiring :
    is-closed-under-left-multiplication-subset-Commutative-Semiring A
      subset-ideal-Commutative-Semiring
  is-closed-under-left-multiplication-ideal-Commutative-Semiring =
    is-closed-under-left-multiplication-ideal-Semiring
      ( semiring-Commutative-Semiring A)
      ( I)

  is-closed-under-right-multiplication-ideal-Commutative-Semiring :
    is-closed-under-right-multiplication-subset-Commutative-Semiring A
      subset-ideal-Commutative-Semiring
  is-closed-under-right-multiplication-ideal-Commutative-Semiring =
    is-closed-under-right-multiplication-right-ideal-Semiring
      ( semiring-Commutative-Semiring A)
      ( right-ideal-ideal-Commutative-Semiring)

  is-closed-under-two-sided-multiplication-ideal-Commutative-Semiring :
    is-closed-under-two-sided-multiplication-subset-Commutative-Semiring A
      subset-ideal-Commutative-Semiring
  is-closed-under-two-sided-multiplication-ideal-Commutative-Semiring =
    is-closed-under-two-sided-multiplication-ideal-Semiring
      ( semiring-Commutative-Semiring A)
      ( two-sided-ideal-ideal-Commutative-Semiring)
```

## Properties

### Characterizing equality of ideals in commutative semirings

```agda
module _
  {l1 l2 l3 : Level}
  (A : Commutative-Semiring l1) (I : ideal-Commutative-Semiring l2 A)
  where

  has-same-elements-ideal-Commutative-Semiring :
    (J : ideal-Commutative-Semiring l3 A) → UU (l1 ⊔ l2 ⊔ l3)
  has-same-elements-ideal-Commutative-Semiring =
    has-same-elements-ideal-Semiring
      ( semiring-Commutative-Semiring A)
      ( I)

module _
  {l1 l2 : Level}
  (A : Commutative-Semiring l1) (I : ideal-Commutative-Semiring l2 A)
  where

  refl-has-same-elements-ideal-Commutative-Semiring :
    has-same-elements-ideal-Commutative-Semiring A I I
  refl-has-same-elements-ideal-Commutative-Semiring =
    refl-has-same-elements-ideal-Semiring
      ( semiring-Commutative-Semiring A)
      ( I)

  is-torsorial-has-same-elements-ideal-Commutative-Semiring :
    is-torsorial (has-same-elements-ideal-Commutative-Semiring A I)
  is-torsorial-has-same-elements-ideal-Commutative-Semiring =
    is-torsorial-has-same-elements-ideal-Semiring
      ( semiring-Commutative-Semiring A)
      ( I)

  has-same-elements-eq-ideal-Commutative-Semiring :
    (J : ideal-Commutative-Semiring l2 A) →
    (I ＝ J) → has-same-elements-ideal-Commutative-Semiring A I J
  has-same-elements-eq-ideal-Commutative-Semiring =
    has-same-elements-eq-ideal-Semiring
      ( semiring-Commutative-Semiring A)
      ( I)

  is-equiv-has-same-elements-eq-ideal-Commutative-Semiring :
    (J : ideal-Commutative-Semiring l2 A) →
    is-equiv (has-same-elements-eq-ideal-Commutative-Semiring J)
  is-equiv-has-same-elements-eq-ideal-Commutative-Semiring =
    is-equiv-has-same-elements-eq-ideal-Semiring
      ( semiring-Commutative-Semiring A)
      ( I)

  extensionality-ideal-Commutative-Semiring :
    (J : ideal-Commutative-Semiring l2 A) →
    (I ＝ J) ≃ has-same-elements-ideal-Commutative-Semiring A I J
  extensionality-ideal-Commutative-Semiring =
    extensionality-ideal-Semiring
      ( semiring-Commutative-Semiring A)
      ( I)

  eq-has-same-elements-ideal-Commutative-Semiring :
    (J : ideal-Commutative-Semiring l2 A) →
    has-same-elements-ideal-Commutative-Semiring A I J → I ＝ J
  eq-has-same-elements-ideal-Commutative-Semiring =
    eq-has-same-elements-ideal-Semiring
      ( semiring-Commutative-Semiring A)
      ( I)
```

