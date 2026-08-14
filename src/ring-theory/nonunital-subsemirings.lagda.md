# Nonunital subsemirings

```agda
module ring-theory.nonunital-subsemirings where
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

An {{#concept "nonunital subsemiring" Disambiguation="in a semiring" Agda=Subsemiring}}
in a [semiring](ring-theory.semirings.md) `R` is an additive submodule of `R`
that is closed under multiplication by elements of `R`.

## Definitions

### Nonunital subsemirings

```agda
is-nonunital-subsemiring-subset-Semiring :
  {l1 l2 : Level} (R : Semiring l1) (P : subset-Semiring l2 R) → UU (l1 ⊔ l2)
is-nonunital-subsemiring-subset-Semiring R P =
  is-additive-submonoid-subset-Semiring R P ×
  ( is-closed-under-multiplication-subset-Semiring R P)

is-prop-is-nonunital-subsemiring-subset-Semiring :
  {l1 l2 : Level} (R : Semiring l1) (P : subset-Semiring l2 R) →
  is-prop (is-nonunital-subsemiring-subset-Semiring R P)
is-prop-is-nonunital-subsemiring-subset-Semiring R P =
  is-prop-product
    ( is-prop-is-additive-submonoid-subset-Semiring R P)
    ( is-prop-is-closed-under-multiplication-subset-Semiring R P)

Nonunital-Subsemiring :
  (l : Level) {l1 : Level} (R : Semiring l1) → UU (lsuc l ⊔ l1)
Nonunital-Subsemiring l R =
  Σ (subset-Semiring l R) (is-nonunital-subsemiring-subset-Semiring R)

module _
  {l1 l2 : Level} (R : Semiring l1) (I : Nonunital-Subsemiring l2 R)
  where

  subset-Nonunital-Subsemiring : subset-Semiring l2 R
  subset-Nonunital-Subsemiring = pr1 I

  is-nonunital-subsemiring-Nonunital-Subsemiring :
    is-nonunital-subsemiring-subset-Semiring R subset-Nonunital-Subsemiring
  is-nonunital-subsemiring-Nonunital-Subsemiring = pr2 I

  is-in-Nonunital-Subsemiring : type-Semiring R → UU l2
  is-in-Nonunital-Subsemiring =
    is-in-subset-Semiring R subset-Nonunital-Subsemiring

  is-prop-is-in-Nonunital-Subsemiring :
    (x : type-Semiring R) → is-prop (is-in-Nonunital-Subsemiring x)
  is-prop-is-in-Nonunital-Subsemiring =
    is-prop-is-in-subset-Semiring R subset-Nonunital-Subsemiring

  type-Nonunital-Subsemiring : UU (l1 ⊔ l2)
  type-Nonunital-Subsemiring =
    type-subset-Semiring R subset-Nonunital-Subsemiring

  inclusion-Nonunital-Subsemiring :
    type-Nonunital-Subsemiring → type-Semiring R
  inclusion-Nonunital-Subsemiring =
    inclusion-subset-Semiring R subset-Nonunital-Subsemiring

  ap-inclusion-Nonunital-Subsemiring :
    (x y : type-Nonunital-Subsemiring) → x ＝ y →
    inclusion-Nonunital-Subsemiring x ＝ inclusion-Nonunital-Subsemiring y
  ap-inclusion-Nonunital-Subsemiring =
    ap-inclusion-subset-Semiring R subset-Nonunital-Subsemiring

  is-in-subset-inclusion-Nonunital-Subsemiring :
    (x : type-Nonunital-Subsemiring) →
    is-in-Nonunital-Subsemiring (inclusion-Nonunital-Subsemiring x)
  is-in-subset-inclusion-Nonunital-Subsemiring =
    is-in-subset-inclusion-subset-Semiring R subset-Nonunital-Subsemiring

  is-closed-under-eq-Nonunital-Subsemiring :
    {x y : type-Semiring R} → is-in-Nonunital-Subsemiring x →
    (x ＝ y) → is-in-Nonunital-Subsemiring y
  is-closed-under-eq-Nonunital-Subsemiring =
    is-closed-under-eq-subset-Semiring R subset-Nonunital-Subsemiring

  is-closed-under-eq-Nonunital-Subsemiring' :
    {x y : type-Semiring R} → is-in-Nonunital-Subsemiring y →
    (x ＝ y) → is-in-Nonunital-Subsemiring x
  is-closed-under-eq-Nonunital-Subsemiring' =
    is-closed-under-eq-subset-Semiring' R subset-Nonunital-Subsemiring

  is-nonunital-subsemiring-subset-Nonunital-Subsemiring :
    is-nonunital-subsemiring-subset-Semiring R subset-Nonunital-Subsemiring
  is-nonunital-subsemiring-subset-Nonunital-Subsemiring = pr2 I

  is-additive-submonoid-Nonunital-Subsemiring :
    is-additive-submonoid-subset-Semiring R subset-Nonunital-Subsemiring
  is-additive-submonoid-Nonunital-Subsemiring =
    pr1 is-nonunital-subsemiring-subset-Nonunital-Subsemiring

  contains-zero-Nonunital-Subsemiring :
    is-in-Nonunital-Subsemiring (zero-Semiring R)
  contains-zero-Nonunital-Subsemiring =
    pr1 is-additive-submonoid-Nonunital-Subsemiring

  zero-Nonunital-Subsemiring : type-Nonunital-Subsemiring
  pr1 zero-Nonunital-Subsemiring = zero-Semiring R
  pr2 zero-Nonunital-Subsemiring = contains-zero-Nonunital-Subsemiring

  is-closed-under-addition-Nonunital-Subsemiring :
    is-closed-under-addition-subset-Semiring R subset-Nonunital-Subsemiring
  is-closed-under-addition-Nonunital-Subsemiring =
    pr2 is-additive-submonoid-Nonunital-Subsemiring

  additive-submonoid-Nonunital-Subsemiring :
    Submonoid l2 (additive-monoid-Semiring R)
  pr1 additive-submonoid-Nonunital-Subsemiring =
    subset-Nonunital-Subsemiring
  pr1 (pr2 additive-submonoid-Nonunital-Subsemiring) =
    contains-zero-Nonunital-Subsemiring
  pr2 (pr2 additive-submonoid-Nonunital-Subsemiring) =
    is-closed-under-addition-Nonunital-Subsemiring

  add-Nonunital-Subsemiring :
    (x y : type-Nonunital-Subsemiring) → type-Nonunital-Subsemiring
  pr1 (add-Nonunital-Subsemiring x y) =
    add-Semiring R
      ( inclusion-Nonunital-Subsemiring x)
      ( inclusion-Nonunital-Subsemiring y)
  pr2 (add-Nonunital-Subsemiring x y) =
    is-closed-under-addition-Nonunital-Subsemiring (pr2 x) (pr2 y)

  is-closed-under-multiplication-Nonunital-Subsemiring :
    is-closed-under-multiplication-subset-Semiring R
      subset-Nonunital-Subsemiring
  is-closed-under-multiplication-Nonunital-Subsemiring =
    pr2 is-nonunital-subsemiring-subset-Nonunital-Subsemiring

  mul-Nonunital-Subsemiring :
    (x y : type-Nonunital-Subsemiring) → type-Nonunital-Subsemiring
  pr1 (mul-Nonunital-Subsemiring x y) =
    mul-Semiring R
      ( inclusion-Nonunital-Subsemiring x)
      ( inclusion-Nonunital-Subsemiring y)
  pr2 (mul-Nonunital-Subsemiring x y) =
    is-closed-under-multiplication-Nonunital-Subsemiring (pr2 x) (pr2 y)
```

## Properties

### Characterizing equality of subsemirings

```agda
module _
  {l1 l2 l3 : Level} (R : Semiring l1) (I : Nonunital-Subsemiring l2 R)
  where

  has-same-elements-Nonunital-Subsemiring :
    (J : Nonunital-Subsemiring l3 R) → UU (l1 ⊔ l2 ⊔ l3)
  has-same-elements-Nonunital-Subsemiring J =
    has-same-elements-subtype
      ( subset-Nonunital-Subsemiring R I)
      ( subset-Nonunital-Subsemiring R J)

module _
  {l1 l2 : Level} (R : Semiring l1) (I : Nonunital-Subsemiring l2 R)
  where

  refl-has-same-elements-Nonunital-Subsemiring :
    has-same-elements-Nonunital-Subsemiring R I I
  refl-has-same-elements-Nonunital-Subsemiring =
    refl-has-same-elements-subtype (subset-Nonunital-Subsemiring R I)

  is-torsorial-has-same-elements-Nonunital-Subsemiring :
    is-torsorial (has-same-elements-Nonunital-Subsemiring R I)
  is-torsorial-has-same-elements-Nonunital-Subsemiring =
    is-torsorial-Eq-subtype
      ( is-torsorial-has-same-elements-subtype
        ( subset-Nonunital-Subsemiring R I))
      ( is-prop-is-nonunital-subsemiring-subset-Semiring R)
      ( subset-Nonunital-Subsemiring R I)
      ( refl-has-same-elements-Nonunital-Subsemiring)
      ( is-nonunital-subsemiring-Nonunital-Subsemiring R I)

  has-same-elements-eq-Nonunital-Subsemiring :
    (J : Nonunital-Subsemiring l2 R) →
    (I ＝ J) → has-same-elements-Nonunital-Subsemiring R I J
  has-same-elements-eq-Nonunital-Subsemiring .I refl =
    refl-has-same-elements-Nonunital-Subsemiring

  is-equiv-has-same-elements-eq-Nonunital-Subsemiring :
    (J : Nonunital-Subsemiring l2 R) →
    is-equiv (has-same-elements-eq-Nonunital-Subsemiring J)
  is-equiv-has-same-elements-eq-Nonunital-Subsemiring =
    fundamental-theorem-id
      is-torsorial-has-same-elements-Nonunital-Subsemiring
      has-same-elements-eq-Nonunital-Subsemiring

  extensionality-Nonunital-Subsemiring :
    (J : Nonunital-Subsemiring l2 R) →
    (I ＝ J) ≃ has-same-elements-Nonunital-Subsemiring R I J
  pr1 (extensionality-Nonunital-Subsemiring J) =
    has-same-elements-eq-Nonunital-Subsemiring J
  pr2 (extensionality-Nonunital-Subsemiring J) =
    is-equiv-has-same-elements-eq-Nonunital-Subsemiring J

  eq-has-same-elements-Nonunital-Subsemiring :
    (J : Nonunital-Subsemiring l2 R) →
    has-same-elements-Nonunital-Subsemiring R I J → I ＝ J
  eq-has-same-elements-Nonunital-Subsemiring J =
    map-inv-equiv (extensionality-Nonunital-Subsemiring J)
```
