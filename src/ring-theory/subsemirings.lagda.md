# Subsemirings

```agda
module ring-theory.subsemirings where
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

open import group-theory.submonoids

open import ring-theory.semirings
open import ring-theory.subsets-semirings
```

</details>

## Idea

An {{#concept "subsemiring" Disambiguation="in a semiring" Agda=Subsemiring}}
in a [semiring](ring-theory.semirings.md) `R` is an additive submodule of `R`
that contains `1` and is closed under multiplication by elements of `R`.

## Definitions

### Subsemirings

```agda
is-subsemiring-subset-Semiring :
  {l1 l2 : Level} (R : Semiring l1) (P : subset-Semiring l2 R) → UU (l1 ⊔ l2)
is-subsemiring-subset-Semiring R P =
  is-additive-submonoid-subset-Semiring R P ×
  contains-one-subset-Semiring R P ×
  is-closed-under-multiplication-subset-Semiring R P

is-prop-is-subsemiring-subset-Semiring :
  {l1 l2 : Level} (R : Semiring l1) (P : subset-Semiring l2 R) →
  is-prop (is-subsemiring-subset-Semiring R P)
is-prop-is-subsemiring-subset-Semiring R P =
  is-prop-product
    ( is-prop-is-additive-submonoid-subset-Semiring R P)
    ( is-prop-product
      ( is-prop-contains-one-subset-Semiring R P)
      ( is-prop-is-closed-under-multiplication-subset-Semiring R P))

Subsemiring :
  (l : Level) {l1 : Level} (R : Semiring l1) → UU (lsuc l ⊔ l1)
Subsemiring l R =
  Σ (subset-Semiring l R) (is-subsemiring-subset-Semiring R)

module _
  {l1 l2 : Level} (R : Semiring l1) (I : Subsemiring l2 R)
  where

  subset-Subsemiring : subset-Semiring l2 R
  subset-Subsemiring = pr1 I

  is-subsemiring-Subsemiring :
    is-subsemiring-subset-Semiring R subset-Subsemiring
  is-subsemiring-Subsemiring = pr2 I

  is-in-Subsemiring : type-Semiring R → UU l2
  is-in-Subsemiring =
    is-in-subset-Semiring R subset-Subsemiring

  is-prop-is-in-Subsemiring :
    (x : type-Semiring R) → is-prop (is-in-Subsemiring x)
  is-prop-is-in-Subsemiring =
    is-prop-is-in-subset-Semiring R subset-Subsemiring

  type-Subsemiring : UU (l1 ⊔ l2)
  type-Subsemiring =
    type-subset-Semiring R subset-Subsemiring

  inclusion-Subsemiring :
    type-Subsemiring → type-Semiring R
  inclusion-Subsemiring =
    inclusion-subset-Semiring R subset-Subsemiring

  ap-inclusion-Subsemiring :
    (x y : type-Subsemiring) → x ＝ y →
    inclusion-Subsemiring x ＝ inclusion-Subsemiring y
  ap-inclusion-Subsemiring =
    ap-inclusion-subset-Semiring R subset-Subsemiring

  is-in-subset-inclusion-Subsemiring :
    (x : type-Subsemiring) →
    is-in-Subsemiring (inclusion-Subsemiring x)
  is-in-subset-inclusion-Subsemiring =
    is-in-subset-inclusion-subset-Semiring R subset-Subsemiring

  is-closed-under-eq-Subsemiring :
    {x y : type-Semiring R} → is-in-Subsemiring x →
    (x ＝ y) → is-in-Subsemiring y
  is-closed-under-eq-Subsemiring =
    is-closed-under-eq-subset-Semiring R subset-Subsemiring

  is-closed-under-eq-Subsemiring' :
    {x y : type-Semiring R} → is-in-Subsemiring y →
    (x ＝ y) → is-in-Subsemiring x
  is-closed-under-eq-Subsemiring' =
    is-closed-under-eq-subset-Semiring' R subset-Subsemiring

  is-subsemiring-subset-Subsemiring :
    is-subsemiring-subset-Semiring R subset-Subsemiring
  is-subsemiring-subset-Subsemiring = pr2 I

  is-additive-submonoid-Subsemiring :
    is-additive-submonoid-subset-Semiring R subset-Subsemiring
  is-additive-submonoid-Subsemiring =
    pr1 is-subsemiring-subset-Subsemiring

  contains-zero-Subsemiring :
    is-in-Subsemiring (zero-Semiring R)
  contains-zero-Subsemiring =
    pr1 is-additive-submonoid-Subsemiring

  zero-Subsemiring : type-Subsemiring
  pr1 zero-Subsemiring = zero-Semiring R
  pr2 zero-Subsemiring = contains-zero-Subsemiring

  is-closed-under-addition-Subsemiring :
    is-closed-under-addition-subset-Semiring R subset-Subsemiring
  is-closed-under-addition-Subsemiring =
    pr2 is-additive-submonoid-Subsemiring

  add-Subsemiring : (x y : type-Subsemiring) → type-Subsemiring
  pr1 (add-Subsemiring x y) =
    add-Semiring R (inclusion-Subsemiring x) (inclusion-Subsemiring y)
  pr2 (add-Subsemiring x y) =
    is-closed-under-addition-Subsemiring (pr2 x) (pr2 y)

  contains-one-Subsemiring :
    is-in-Subsemiring (one-Semiring R)
  contains-one-Subsemiring =
    pr1 (pr2 is-subsemiring-subset-Subsemiring)

  one-Subsemiring : type-Subsemiring
  pr1 one-Subsemiring = one-Semiring R
  pr2 one-Subsemiring = contains-one-Subsemiring

  is-closed-under-multiplication-Subsemiring :
    is-closed-under-multiplication-subset-Semiring R subset-Subsemiring
  is-closed-under-multiplication-Subsemiring =
    pr2 (pr2 is-subsemiring-subset-Subsemiring)

  mul-Subsemiring : (x y : type-Subsemiring) → type-Subsemiring
  pr1 (mul-Subsemiring x y) =
    mul-Semiring R (inclusion-Subsemiring x) (inclusion-Subsemiring y)
  pr2 (mul-Subsemiring x y) =
    is-closed-under-multiplication-Subsemiring (pr2 x) (pr2 y)

  additive-submonoid-Subsemiring : Submonoid l2 (additive-monoid-Semiring R)
  pr1 additive-submonoid-Subsemiring =
    subset-Subsemiring
  pr1 (pr2 additive-submonoid-Subsemiring) =
    contains-zero-Subsemiring
  pr2 (pr2 additive-submonoid-Subsemiring) =
    is-closed-under-addition-Subsemiring
```

## Properties

### Characterizing equality of subsemirings

```agda
module _
  {l1 l2 l3 : Level} (R : Semiring l1) (I : Subsemiring l2 R)
  where

  has-same-elements-Subsemiring :
    (J : Subsemiring l3 R) → UU (l1 ⊔ l2 ⊔ l3)
  has-same-elements-Subsemiring J =
    has-same-elements-subtype
      ( subset-Subsemiring R I)
      ( subset-Subsemiring R J)

module _
  {l1 l2 : Level} (R : Semiring l1) (I : Subsemiring l2 R)
  where

  refl-has-same-elements-Subsemiring :
    has-same-elements-Subsemiring R I I
  refl-has-same-elements-Subsemiring =
    refl-has-same-elements-subtype (subset-Subsemiring R I)

  is-torsorial-has-same-elements-Subsemiring :
    is-torsorial (has-same-elements-Subsemiring R I)
  is-torsorial-has-same-elements-Subsemiring =
    is-torsorial-Eq-subtype
      ( is-torsorial-has-same-elements-subtype (subset-Subsemiring R I))
      ( is-prop-is-subsemiring-subset-Semiring R)
      ( subset-Subsemiring R I)
      ( refl-has-same-elements-Subsemiring)
      ( is-subsemiring-Subsemiring R I)

  has-same-elements-eq-Subsemiring :
    (J : Subsemiring l2 R) →
    (I ＝ J) → has-same-elements-Subsemiring R I J
  has-same-elements-eq-Subsemiring .I refl =
    refl-has-same-elements-Subsemiring

  is-equiv-has-same-elements-eq-Subsemiring :
    (J : Subsemiring l2 R) → is-equiv (has-same-elements-eq-Subsemiring J)
  is-equiv-has-same-elements-eq-Subsemiring =
    fundamental-theorem-id
      is-torsorial-has-same-elements-Subsemiring
      has-same-elements-eq-Subsemiring

  extensionality-Subsemiring :
    (J : Subsemiring l2 R) →
    (I ＝ J) ≃ has-same-elements-Subsemiring R I J
  pr1 (extensionality-Subsemiring J) =
    has-same-elements-eq-Subsemiring J
  pr2 (extensionality-Subsemiring J) =
    is-equiv-has-same-elements-eq-Subsemiring J

  eq-has-same-elements-Subsemiring :
    (J : Subsemiring l2 R) → has-same-elements-Subsemiring R I J → I ＝ J
  eq-has-same-elements-Subsemiring J =
    map-inv-equiv (extensionality-Subsemiring J)
```
