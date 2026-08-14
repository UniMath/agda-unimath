# Nonunital subrings

```agda
module ring-theory.nonunital-subrings where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtype-identity-principle
open import foundation.subtypes
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import group-theory.subgroups
open import group-theory.submonoids

open import ring-theory.rings
open import ring-theory.subsets-rings
```

</details>

## Idea

An {{#concept "nonunital subring" Disambiguation="in a ring" Agda=Subring}}
in a [ring](ring-theory.rings.md) `R` is an additive submodule of `R`
that is closed under multiplication by elements of `R`.

## Definitions

### Nonunital subrings

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (P : subset-Ring l2 R)
  where
  
  is-nonunital-subring-subset-Ring :
    UU (l1 ⊔ l2)
  is-nonunital-subring-subset-Ring =
    is-additive-subgroup-subset-Ring R P ×
    is-closed-under-multiplication-subset-Ring R P

  is-prop-is-nonunital-subring-subset-Ring :
    is-prop is-nonunital-subring-subset-Ring
  is-prop-is-nonunital-subring-subset-Ring =
    is-prop-product
      ( is-prop-is-additive-subgroup-subset-Ring R P)
      ( is-prop-is-closed-under-multiplication-subset-Ring R P)

  is-nonunital-subring-prop-subset-Ring :
    Prop (l1 ⊔ l2)
  pr1 is-nonunital-subring-prop-subset-Ring =
    is-nonunital-subring-subset-Ring
  pr2 is-nonunital-subring-prop-subset-Ring =
    is-prop-is-nonunital-subring-subset-Ring

Nonunital-Subring :
  (l : Level) {l1 : Level} (R : Ring l1) → UU (lsuc l ⊔ l1)
Nonunital-Subring l R =
  Σ (subset-Ring l R) (is-nonunital-subring-subset-Ring R)

module _
  {l1 l2 : Level} (R : Ring l1) (I : Nonunital-Subring l2 R)
  where

  subset-Nonunital-Subring : subset-Ring l2 R
  subset-Nonunital-Subring = pr1 I

  is-nonunital-subring-Nonunital-Subring :
    is-nonunital-subring-subset-Ring R subset-Nonunital-Subring
  is-nonunital-subring-Nonunital-Subring = pr2 I

  is-in-Nonunital-Subring : type-Ring R → UU l2
  is-in-Nonunital-Subring =
    is-in-subset-Ring R subset-Nonunital-Subring

  is-prop-is-in-Nonunital-Subring :
    (x : type-Ring R) → is-prop (is-in-Nonunital-Subring x)
  is-prop-is-in-Nonunital-Subring =
    is-prop-is-in-subset-Ring R subset-Nonunital-Subring

  type-Nonunital-Subring : UU (l1 ⊔ l2)
  type-Nonunital-Subring =
    type-subset-Ring R subset-Nonunital-Subring

  inclusion-Nonunital-Subring :
    type-Nonunital-Subring → type-Ring R
  inclusion-Nonunital-Subring =
    inclusion-subset-Ring R subset-Nonunital-Subring

  ap-inclusion-Nonunital-Subring :
    (x y : type-Nonunital-Subring) → x ＝ y →
    inclusion-Nonunital-Subring x ＝ inclusion-Nonunital-Subring y
  ap-inclusion-Nonunital-Subring =
    ap-inclusion-subset-Ring R subset-Nonunital-Subring

  is-in-subset-inclusion-Nonunital-Subring :
    (x : type-Nonunital-Subring) →
    is-in-Nonunital-Subring (inclusion-Nonunital-Subring x)
  is-in-subset-inclusion-Nonunital-Subring =
    is-in-subset-inclusion-subset-Ring R subset-Nonunital-Subring

  is-closed-under-eq-Nonunital-Subring :
    {x y : type-Ring R} → is-in-Nonunital-Subring x →
    (x ＝ y) → is-in-Nonunital-Subring y
  is-closed-under-eq-Nonunital-Subring =
    is-closed-under-eq-subset-Ring R subset-Nonunital-Subring

  is-closed-under-eq-Nonunital-Subring' :
    {x y : type-Ring R} → is-in-Nonunital-Subring y →
    (x ＝ y) → is-in-Nonunital-Subring x
  is-closed-under-eq-Nonunital-Subring' =
    is-closed-under-eq-subset-Ring' R subset-Nonunital-Subring

  is-nonunital-subring-subset-Nonunital-Subring :
    is-nonunital-subring-subset-Ring R subset-Nonunital-Subring
  is-nonunital-subring-subset-Nonunital-Subring = pr2 I

  is-additive-subgroup-Nonunital-Subring :
    is-additive-subgroup-subset-Ring R subset-Nonunital-Subring
  is-additive-subgroup-Nonunital-Subring =
    pr1 is-nonunital-subring-subset-Nonunital-Subring

  contains-zero-Nonunital-Subring :
    is-in-Nonunital-Subring (zero-Ring R)
  contains-zero-Nonunital-Subring =
    pr1 is-additive-subgroup-Nonunital-Subring

  is-closed-under-addition-Nonunital-Subring :
    is-closed-under-addition-subset-Ring R subset-Nonunital-Subring
  is-closed-under-addition-Nonunital-Subring =
    pr1 (pr2 is-additive-subgroup-Nonunital-Subring)

  is-closed-under-negatives-Nonunital-Subring :
    is-closed-under-negatives-subset-Ring R subset-Nonunital-Subring
  is-closed-under-negatives-Nonunital-Subring =
    pr2 (pr2 is-additive-subgroup-Nonunital-Subring)

  additive-submonoid-Nonunital-Subring :
    Submonoid l2 (additive-monoid-Ring R)
  pr1 additive-submonoid-Nonunital-Subring =
    subset-Nonunital-Subring
  pr1 (pr2 additive-submonoid-Nonunital-Subring) =
    contains-zero-Nonunital-Subring
  pr2 (pr2 additive-submonoid-Nonunital-Subring) =
    is-closed-under-addition-Nonunital-Subring

  additive-subgroup-Nonunital-Subring :
    Subgroup l2 (group-Ring R)
  pr1 additive-subgroup-Nonunital-Subring =
    subset-Nonunital-Subring
  pr1 (pr2 additive-subgroup-Nonunital-Subring) =
    contains-zero-Nonunital-Subring
  pr1 (pr2 (pr2 additive-subgroup-Nonunital-Subring)) =
    is-closed-under-addition-Nonunital-Subring
  pr2 (pr2 (pr2 additive-subgroup-Nonunital-Subring)) =
    is-closed-under-negatives-Nonunital-Subring

  is-closed-under-multiplication-Nonunital-Subring :
    is-closed-under-multiplication-subset-Ring R
      subset-Nonunital-Subring
  is-closed-under-multiplication-Nonunital-Subring =
    pr2 is-nonunital-subring-subset-Nonunital-Subring
```

## Properties

### Characterizing equality of subrings

```agda
module _
  {l1 l2 l3 : Level} (R : Ring l1) (I : Nonunital-Subring l2 R)
  where

  has-same-elements-Nonunital-Subring :
    (J : Nonunital-Subring l3 R) → UU (l1 ⊔ l2 ⊔ l3)
  has-same-elements-Nonunital-Subring J =
    has-same-elements-subtype
      ( subset-Nonunital-Subring R I)
      ( subset-Nonunital-Subring R J)

module _
  {l1 l2 : Level} (R : Ring l1) (I : Nonunital-Subring l2 R)
  where

  refl-has-same-elements-Nonunital-Subring :
    has-same-elements-Nonunital-Subring R I I
  refl-has-same-elements-Nonunital-Subring =
    refl-has-same-elements-subtype (subset-Nonunital-Subring R I)

  is-torsorial-has-same-elements-Nonunital-Subring :
    is-torsorial (has-same-elements-Nonunital-Subring R I)
  is-torsorial-has-same-elements-Nonunital-Subring =
    is-torsorial-Eq-subtype
      ( is-torsorial-has-same-elements-subtype
        ( subset-Nonunital-Subring R I))
      ( is-prop-is-nonunital-subring-subset-Ring R)
      ( subset-Nonunital-Subring R I)
      ( refl-has-same-elements-Nonunital-Subring)
      ( is-nonunital-subring-Nonunital-Subring R I)

  has-same-elements-eq-Nonunital-Subring :
    (J : Nonunital-Subring l2 R) →
    (I ＝ J) → has-same-elements-Nonunital-Subring R I J
  has-same-elements-eq-Nonunital-Subring .I refl =
    refl-has-same-elements-Nonunital-Subring

  is-equiv-has-same-elements-eq-Nonunital-Subring :
    (J : Nonunital-Subring l2 R) →
    is-equiv (has-same-elements-eq-Nonunital-Subring J)
  is-equiv-has-same-elements-eq-Nonunital-Subring =
    fundamental-theorem-id
      is-torsorial-has-same-elements-Nonunital-Subring
      has-same-elements-eq-Nonunital-Subring

  extensionality-Nonunital-Subring :
    (J : Nonunital-Subring l2 R) →
    (I ＝ J) ≃ has-same-elements-Nonunital-Subring R I J
  pr1 (extensionality-Nonunital-Subring J) =
    has-same-elements-eq-Nonunital-Subring J
  pr2 (extensionality-Nonunital-Subring J) =
    is-equiv-has-same-elements-eq-Nonunital-Subring J

  eq-has-same-elements-Nonunital-Subring :
    (J : Nonunital-Subring l2 R) →
    has-same-elements-Nonunital-Subring R I J → I ＝ J
  eq-has-same-elements-Nonunital-Subring J =
    map-inv-equiv (extensionality-Nonunital-Subring J)
```
