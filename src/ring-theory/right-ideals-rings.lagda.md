# Right ideals of rings

```agda
module ring-theory.right-ideals-rings where
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

open import ring-theory.rings
open import ring-theory.subsets-rings
```

</details>

## Idea

A {{#concept "right ideal" Disambiguation="in a ring" Agda=right-ideal-Ring}} in
a [ring](ring-theory.rings.md) `R` is a right submodule of `R`.

## Definitions

### Right ideals

```agda
module _
  {l1 : Level} (R : Ring l1)
  where

  is-right-ideal-subset-Ring :
    {l2 : Level} → subset-Ring l2 R → UU (l1 ⊔ l2)
  is-right-ideal-subset-Ring P =
    is-additive-subgroup-subset-Ring R P ×
    is-closed-under-right-multiplication-subset-Ring R P

  is-prop-is-right-ideal-subset-Ring :
    {l2 : Level} (S : subset-Ring l2 R) → is-prop (is-right-ideal-subset-Ring S)
  is-prop-is-right-ideal-subset-Ring S =
    is-prop-product
      ( is-prop-is-additive-subgroup-subset-Ring R S)
      ( is-prop-is-closed-under-right-multiplication-subset-Ring R S)

right-ideal-Ring :
  (l : Level) {l1 : Level} (R : Ring l1) → UU (lsuc l ⊔ l1)
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

  ap-inclusion-right-ideal-Ring :
    (x y : type-right-ideal-Ring) → x ＝ y →
    inclusion-right-ideal-Ring x ＝ inclusion-right-ideal-Ring y
  ap-inclusion-right-ideal-Ring =
    ap-inclusion-subset-Ring R subset-right-ideal-Ring

  is-in-subset-inclusion-right-ideal-Ring :
    (x : type-right-ideal-Ring) →
    is-in-right-ideal-Ring (inclusion-right-ideal-Ring x)
  is-in-subset-inclusion-right-ideal-Ring =
    is-in-subset-inclusion-subset-Ring R subset-right-ideal-Ring

  is-closed-under-eq-right-ideal-Ring :
    {x y : type-Ring R} → is-in-right-ideal-Ring x →
    (x ＝ y) → is-in-right-ideal-Ring y
  is-closed-under-eq-right-ideal-Ring =
    is-closed-under-eq-subset-Ring R subset-right-ideal-Ring

  is-closed-under-eq-right-ideal-Ring' :
    {x y : type-Ring R} → is-in-right-ideal-Ring y →
    (x ＝ y) → is-in-right-ideal-Ring x
  is-closed-under-eq-right-ideal-Ring' =
    is-closed-under-eq-subset-Ring' R subset-right-ideal-Ring

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

  is-closed-under-addition-right-ideal-Ring :
    is-closed-under-addition-subset-Ring R subset-right-ideal-Ring
  is-closed-under-addition-right-ideal-Ring =
    pr1 (pr2 is-additive-subgroup-subset-right-ideal-Ring)

  is-closed-under-negatives-right-ideal-Ring :
    is-closed-under-negatives-subset-Ring R subset-right-ideal-Ring
  is-closed-under-negatives-right-ideal-Ring =
    pr2 (pr2 is-additive-subgroup-subset-right-ideal-Ring)

  is-closed-under-right-multiplication-right-ideal-Ring :
    is-closed-under-right-multiplication-subset-Ring R subset-right-ideal-Ring
  is-closed-under-right-multiplication-right-ideal-Ring =
    pr2 is-right-ideal-subset-right-ideal-Ring

  is-right-ideal-right-ideal-Ring :
    is-right-ideal-subset-Ring R subset-right-ideal-Ring
  is-right-ideal-right-ideal-Ring = pr2 I
```

## Properties

### Characterizing equality of right ideals in rings

```agda
module _
  {l1 l2 l3 : Level} (R : Ring l1) (I : right-ideal-Ring l2 R)
  where

  has-same-elements-right-ideal-Ring :
    (J : right-ideal-Ring l3 R) → UU (l1 ⊔ l2 ⊔ l3)
  has-same-elements-right-ideal-Ring J =
    has-same-elements-subtype
      ( subset-right-ideal-Ring R I)
      ( subset-right-ideal-Ring R J)

module _
  {l1 l2 : Level} (R : Ring l1) (I : right-ideal-Ring l2 R)
  where

  refl-has-same-elements-right-ideal-Ring :
    has-same-elements-right-ideal-Ring R I I
  refl-has-same-elements-right-ideal-Ring =
    refl-has-same-elements-subtype (subset-right-ideal-Ring R I)

  is-torsorial-has-same-elements-right-ideal-Ring :
    is-torsorial (has-same-elements-right-ideal-Ring R I)
  is-torsorial-has-same-elements-right-ideal-Ring =
    is-torsorial-Eq-subtype
      ( is-torsorial-has-same-elements-subtype (subset-right-ideal-Ring R I))
      ( is-prop-is-right-ideal-subset-Ring R)
      ( subset-right-ideal-Ring R I)
      ( refl-has-same-elements-right-ideal-Ring)
      ( is-right-ideal-right-ideal-Ring R I)

  has-same-elements-eq-right-ideal-Ring :
    (J : right-ideal-Ring l2 R) →
    (I ＝ J) → has-same-elements-right-ideal-Ring R I J
  has-same-elements-eq-right-ideal-Ring .I refl =
    refl-has-same-elements-right-ideal-Ring

  is-equiv-has-same-elements-eq-right-ideal-Ring :
    (J : right-ideal-Ring l2 R) →
    is-equiv (has-same-elements-eq-right-ideal-Ring J)
  is-equiv-has-same-elements-eq-right-ideal-Ring =
    fundamental-theorem-id
      is-torsorial-has-same-elements-right-ideal-Ring
      has-same-elements-eq-right-ideal-Ring

  extensionality-right-ideal-Ring :
    (J : right-ideal-Ring l2 R) →
    (I ＝ J) ≃ has-same-elements-right-ideal-Ring R I J
  pr1 (extensionality-right-ideal-Ring J) =
    has-same-elements-eq-right-ideal-Ring J
  pr2 (extensionality-right-ideal-Ring J) =
    is-equiv-has-same-elements-eq-right-ideal-Ring J

  eq-has-same-elements-right-ideal-Ring :
    (J : right-ideal-Ring l2 R) →
    has-same-elements-right-ideal-Ring R I J → I ＝ J
  eq-has-same-elements-right-ideal-Ring J =
    map-inv-equiv (extensionality-right-ideal-Ring J)
```
