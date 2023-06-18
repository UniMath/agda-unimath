# Ideals of rings

```agda
module ring-theory.ideals-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtype-identity-principle
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.subgroups-abelian-groups

open import ring-theory.left-ideals-rings
open import ring-theory.right-ideals-rings
open import ring-theory.rings
open import ring-theory.subsets-rings
```

</details>

## Idea

An **ideal** in a [ring](ring-theory.rings.md) `R` is a submodule of `R`.

## Definitions

### Two-sided ideals

```agda
is-ideal-subset-Ring :
  {l1 l2 : Level} (R : Ring l1) (P : subset-Ring l2 R) → UU (l1 ⊔ l2)
is-ideal-subset-Ring R P =
  is-additive-subgroup-subset-Ring R P ×
  ( is-closed-under-left-multiplication-subset-Ring R P ×
    is-closed-under-right-multiplication-subset-Ring R P)

is-prop-is-ideal-subset-Ring :
  {l1 l2 : Level} (R : Ring l1) (P : subset-Ring l2 R) →
  is-prop (is-ideal-subset-Ring R P)
is-prop-is-ideal-subset-Ring R P =
  is-prop-prod
    ( is-prop-is-additive-subgroup-subset-Ring R P)
    ( is-prop-prod
      ( is-prop-is-closed-under-left-multiplication-subset-Ring R P)
      ( is-prop-is-closed-under-right-multiplication-subset-Ring R P))

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

  is-ideal-ideal-Ring :
    is-ideal-subset-Ring R subset-ideal-Ring
  is-ideal-ideal-Ring = pr2 I

  is-additive-subgroup-ideal-Ring :
    is-additive-subgroup-subset-Ring R subset-ideal-Ring
  is-additive-subgroup-ideal-Ring =
    pr1 is-ideal-ideal-Ring

  contains-zero-ideal-Ring : contains-zero-subset-Ring R subset-ideal-Ring
  contains-zero-ideal-Ring = pr1 is-additive-subgroup-ideal-Ring

  is-closed-under-addition-ideal-Ring :
    is-closed-under-addition-subset-Ring R subset-ideal-Ring
  is-closed-under-addition-ideal-Ring =
    pr1 (pr2 is-additive-subgroup-ideal-Ring)

  is-closed-under-negatives-ideal-Ring :
    is-closed-under-negatives-subset-Ring R subset-ideal-Ring
  is-closed-under-negatives-ideal-Ring =
    pr2 (pr2 is-additive-subgroup-ideal-Ring)

  is-closed-under-left-multiplication-ideal-Ring :
    is-closed-under-left-multiplication-subset-Ring R subset-ideal-Ring
  is-closed-under-left-multiplication-ideal-Ring =
    pr1 (pr2 is-ideal-ideal-Ring)

  is-closed-under-right-multiplication-ideal-Ring :
    is-closed-under-right-multiplication-subset-Ring R subset-ideal-Ring
  is-closed-under-right-multiplication-ideal-Ring =
    pr2 (pr2 is-ideal-ideal-Ring)

  subgroup-ideal-Ring : Subgroup-Ab l2 (ab-Ring R)
  pr1 subgroup-ideal-Ring = subset-ideal-Ring
  pr1 (pr2 subgroup-ideal-Ring) = contains-zero-ideal-Ring
  pr1 (pr2 (pr2 subgroup-ideal-Ring)) = is-closed-under-addition-ideal-Ring
  pr2 (pr2 (pr2 subgroup-ideal-Ring)) = is-closed-under-negatives-ideal-Ring

  normal-subgroup-ideal-Ring : Normal-Subgroup-Ab l2 (ab-Ring R)
  normal-subgroup-ideal-Ring =
    normal-subgroup-Subgroup-Ab (ab-Ring R) subgroup-ideal-Ring

  left-ideal-ideal-Ring : left-ideal-Ring l2 R
  pr1 left-ideal-ideal-Ring = subset-ideal-Ring
  pr1 (pr2 left-ideal-ideal-Ring) = is-additive-subgroup-ideal-Ring
  pr2 (pr2 left-ideal-ideal-Ring) =
    is-closed-under-left-multiplication-ideal-Ring

  right-ideal-ideal-Ring : right-ideal-Ring l2 R
  pr1 right-ideal-ideal-Ring = subset-ideal-Ring
  pr1 (pr2 right-ideal-ideal-Ring) = is-additive-subgroup-ideal-Ring
  pr2 (pr2 right-ideal-ideal-Ring) =
    is-closed-under-right-multiplication-ideal-Ring
```

## Properties

### Characterizing equality of ideals in rings

```agda
module _
  {l1 l2 l3 : Level} (R : Ring l1) (I : ideal-Ring l2 R)
  where

  has-same-elements-ideal-Ring : (J : ideal-Ring l3 R) → UU (l1 ⊔ l2 ⊔ l3)
  has-same-elements-ideal-Ring J =
    has-same-elements-subtype (subset-ideal-Ring R I) (subset-ideal-Ring R J)

module _
  {l1 l2 : Level} (R : Ring l1) (I : ideal-Ring l2 R)
  where

  refl-has-same-elements-ideal-Ring :
    has-same-elements-ideal-Ring R I I
  refl-has-same-elements-ideal-Ring =
    refl-has-same-elements-subtype (subset-ideal-Ring R I)

  is-contr-total-has-same-elements-ideal-Ring :
    is-contr (Σ (ideal-Ring l2 R) (has-same-elements-ideal-Ring R I))
  is-contr-total-has-same-elements-ideal-Ring =
    is-contr-total-Eq-subtype
      ( is-contr-total-has-same-elements-subtype (subset-ideal-Ring R I))
      ( is-prop-is-ideal-subset-Ring R)
      ( subset-ideal-Ring R I)
      ( refl-has-same-elements-ideal-Ring)
      ( is-ideal-ideal-Ring R I)

  has-same-elements-eq-ideal-Ring :
    (J : ideal-Ring l2 R) → (I ＝ J) → has-same-elements-ideal-Ring R I J
  has-same-elements-eq-ideal-Ring .I refl = refl-has-same-elements-ideal-Ring

  is-equiv-has-same-elements-eq-ideal-Ring :
    (J : ideal-Ring l2 R) → is-equiv (has-same-elements-eq-ideal-Ring J)
  is-equiv-has-same-elements-eq-ideal-Ring =
    fundamental-theorem-id
      is-contr-total-has-same-elements-ideal-Ring
      has-same-elements-eq-ideal-Ring

  extensionality-ideal-Ring :
    (J : ideal-Ring l2 R) → (I ＝ J) ≃ has-same-elements-ideal-Ring R I J
  pr1 (extensionality-ideal-Ring J) = has-same-elements-eq-ideal-Ring J
  pr2 (extensionality-ideal-Ring J) = is-equiv-has-same-elements-eq-ideal-Ring J

  eq-has-same-elements-ideal-Ring :
    (J : ideal-Ring l2 R) → has-same-elements-ideal-Ring R I J → I ＝ J
  eq-has-same-elements-ideal-Ring J =
    map-inv-equiv (extensionality-ideal-Ring J)
```
