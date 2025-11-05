# Left ideals of rings

```agda
module ring-theory.left-ideals-rings where
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

A {{#concept "left ideal" Disambiguation="in a ring" Agda=left-ideal-Ring}} in a
[ring](ring-theory.rings.md) `R` is a left submodule of `R`.

## Definitions

### Left ideals

```agda
module _
  {l1 : Level} (R : Ring l1)
  where

  is-left-ideal-subset-Ring :
    {l2 : Level} → subset-Ring l2 R → UU (l1 ⊔ l2)
  is-left-ideal-subset-Ring S =
    is-additive-subgroup-subset-Ring R S ×
    is-closed-under-left-multiplication-subset-Ring R S

  is-prop-is-left-ideal-subset-Ring :
    {l2 : Level} (S : subset-Ring l2 R) → is-prop (is-left-ideal-subset-Ring S)
  is-prop-is-left-ideal-subset-Ring S =
    is-prop-product
      ( is-prop-is-additive-subgroup-subset-Ring R S)
      ( is-prop-is-closed-under-left-multiplication-subset-Ring R S)

left-ideal-Ring :
  (l : Level) {l1 : Level} (R : Ring l1) → UU (lsuc l ⊔ l1)
left-ideal-Ring l R = Σ (subset-Ring l R) (is-left-ideal-subset-Ring R)

module _
  {l1 l2 : Level} (R : Ring l1) (I : left-ideal-Ring l2 R)
  where

  subset-left-ideal-Ring : subset-Ring l2 R
  subset-left-ideal-Ring = pr1 I

  is-in-left-ideal-Ring : type-Ring R → UU l2
  is-in-left-ideal-Ring x = type-Prop (subset-left-ideal-Ring x)

  type-left-ideal-Ring : UU (l1 ⊔ l2)
  type-left-ideal-Ring = type-subset-Ring R subset-left-ideal-Ring

  inclusion-left-ideal-Ring : type-left-ideal-Ring → type-Ring R
  inclusion-left-ideal-Ring = inclusion-subset-Ring R subset-left-ideal-Ring

  ap-inclusion-left-ideal-Ring :
    (x y : type-left-ideal-Ring) → x ＝ y →
    inclusion-left-ideal-Ring x ＝ inclusion-left-ideal-Ring y
  ap-inclusion-left-ideal-Ring =
    ap-inclusion-subset-Ring R subset-left-ideal-Ring

  is-in-subset-inclusion-left-ideal-Ring :
    (x : type-left-ideal-Ring) →
    is-in-left-ideal-Ring (inclusion-left-ideal-Ring x)
  is-in-subset-inclusion-left-ideal-Ring =
    is-in-subset-inclusion-subset-Ring R subset-left-ideal-Ring

  is-closed-under-eq-left-ideal-Ring :
    {x y : type-Ring R} → is-in-left-ideal-Ring x →
    (x ＝ y) → is-in-left-ideal-Ring y
  is-closed-under-eq-left-ideal-Ring =
    is-closed-under-eq-subset-Ring R subset-left-ideal-Ring

  is-closed-under-eq-left-ideal-Ring' :
    {x y : type-Ring R} → is-in-left-ideal-Ring y →
    (x ＝ y) → is-in-left-ideal-Ring x
  is-closed-under-eq-left-ideal-Ring' =
    is-closed-under-eq-subset-Ring' R subset-left-ideal-Ring

  is-left-ideal-subset-left-ideal-Ring :
    is-left-ideal-subset-Ring R subset-left-ideal-Ring
  is-left-ideal-subset-left-ideal-Ring = pr2 I

  is-additive-subgroup-subset-left-ideal-Ring :
    is-additive-subgroup-subset-Ring R subset-left-ideal-Ring
  is-additive-subgroup-subset-left-ideal-Ring =
    pr1 is-left-ideal-subset-left-ideal-Ring

  contains-zero-left-ideal-Ring : is-in-left-ideal-Ring (zero-Ring R)
  contains-zero-left-ideal-Ring =
    pr1 is-additive-subgroup-subset-left-ideal-Ring

  is-closed-under-addition-left-ideal-Ring :
    is-closed-under-addition-subset-Ring R subset-left-ideal-Ring
  is-closed-under-addition-left-ideal-Ring =
    pr1 (pr2 is-additive-subgroup-subset-left-ideal-Ring)

  is-closed-under-negatives-left-ideal-Ring :
    is-closed-under-negatives-subset-Ring R subset-left-ideal-Ring
  is-closed-under-negatives-left-ideal-Ring =
    pr2 (pr2 is-additive-subgroup-subset-left-ideal-Ring)

  is-closed-under-left-multiplication-left-ideal-Ring :
    is-closed-under-left-multiplication-subset-Ring R subset-left-ideal-Ring
  is-closed-under-left-multiplication-left-ideal-Ring =
    pr2 is-left-ideal-subset-left-ideal-Ring

  is-left-ideal-left-ideal-Ring :
    is-left-ideal-subset-Ring R subset-left-ideal-Ring
  is-left-ideal-left-ideal-Ring = pr2 I
```

## Properties

### Characterizing equality of left ideals in rings

```agda
module _
  {l1 l2 l3 : Level} (R : Ring l1) (I : left-ideal-Ring l2 R)
  where

  has-same-elements-left-ideal-Ring :
    (J : left-ideal-Ring l3 R) → UU (l1 ⊔ l2 ⊔ l3)
  has-same-elements-left-ideal-Ring J =
    has-same-elements-subtype
      ( subset-left-ideal-Ring R I)
      ( subset-left-ideal-Ring R J)

module _
  {l1 l2 : Level} (R : Ring l1) (I : left-ideal-Ring l2 R)
  where

  refl-has-same-elements-left-ideal-Ring :
    has-same-elements-left-ideal-Ring R I I
  refl-has-same-elements-left-ideal-Ring =
    refl-has-same-elements-subtype (subset-left-ideal-Ring R I)

  is-torsorial-has-same-elements-left-ideal-Ring :
    is-torsorial (has-same-elements-left-ideal-Ring R I)
  is-torsorial-has-same-elements-left-ideal-Ring =
    is-torsorial-Eq-subtype
      ( is-torsorial-has-same-elements-subtype (subset-left-ideal-Ring R I))
      ( is-prop-is-left-ideal-subset-Ring R)
      ( subset-left-ideal-Ring R I)
      ( refl-has-same-elements-left-ideal-Ring)
      ( is-left-ideal-left-ideal-Ring R I)

  has-same-elements-eq-left-ideal-Ring :
    (J : left-ideal-Ring l2 R) →
    (I ＝ J) → has-same-elements-left-ideal-Ring R I J
  has-same-elements-eq-left-ideal-Ring .I refl =
    refl-has-same-elements-left-ideal-Ring

  is-equiv-has-same-elements-eq-left-ideal-Ring :
    (J : left-ideal-Ring l2 R) →
    is-equiv (has-same-elements-eq-left-ideal-Ring J)
  is-equiv-has-same-elements-eq-left-ideal-Ring =
    fundamental-theorem-id
      is-torsorial-has-same-elements-left-ideal-Ring
      has-same-elements-eq-left-ideal-Ring

  extensionality-left-ideal-Ring :
    (J : left-ideal-Ring l2 R) →
    (I ＝ J) ≃ has-same-elements-left-ideal-Ring R I J
  pr1 (extensionality-left-ideal-Ring J) =
    has-same-elements-eq-left-ideal-Ring J
  pr2 (extensionality-left-ideal-Ring J) =
    is-equiv-has-same-elements-eq-left-ideal-Ring J

  eq-has-same-elements-left-ideal-Ring :
    (J : left-ideal-Ring l2 R) →
    has-same-elements-left-ideal-Ring R I J → I ＝ J
  eq-has-same-elements-left-ideal-Ring J =
    map-inv-equiv (extensionality-left-ideal-Ring J)
```
