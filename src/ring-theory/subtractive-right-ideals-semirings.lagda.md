# Subtractive right ideals of semirings

```agda
module ring-theory.subtractive-right-ideals-semirings where
```

<details><summary>Imports</summary>

```agda
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

open import ring-theory.right-ideals-semirings
open import ring-theory.nonunital-subsemirings
open import ring-theory.semirings
open import ring-theory.subsets-semirings
open import ring-theory.subtractive-subsets-semirings
```

</details>

## Idea

A [right ideal](ring-theory.right-ideals-semirings.md) `I` of a [semiring](ring-theory.semirings.md) `R` is said to be
{{#concept "subtractive" Disambiguation="right ideal of a semiring" Agda=subtractive-right-ideal-Semiring}}
if for any `x y ∈ R` we have

```text
  x ∈ I ⇒ x + y ∈ I ⇒ y ∈ I.
```

That is, a subtractive right ideal is a right ideal satisfying a 3-for-2 property.

## Definitions

### The predicate of being a subtractive right ideal

```agda
module _
  {l1 l2 : Level} (R : Semiring l1) (I : right-ideal-Semiring l2 R)
  where

  is-subtractive-right-ideal-Semiring :
    UU (l1 ⊔ l2)
  is-subtractive-right-ideal-Semiring =
    is-subtractive-subset-Semiring R (subset-right-ideal-Semiring R I)

  is-prop-is-subtractive-right-ideal-Semiring :
    is-prop is-subtractive-right-ideal-Semiring
  is-prop-is-subtractive-right-ideal-Semiring =
    is-prop-is-subtractive-subset-Semiring R (subset-right-ideal-Semiring R I)

  is-subtractive-prop-right-ideal-Semiring :
    Prop (l1 ⊔ l2)
  pr1 is-subtractive-prop-right-ideal-Semiring =
    is-subtractive-right-ideal-Semiring
  pr2 is-subtractive-prop-right-ideal-Semiring =
    is-prop-is-subtractive-right-ideal-Semiring
```

### The type of subtractive right ideals

```agda
subtractive-right-ideal-Semiring :
  {l1 : Level} (l2 : Level) (R : Semiring l1) → UU (l1 ⊔ lsuc l2)
subtractive-right-ideal-Semiring l2 R =
  Σ (right-ideal-Semiring l2 R) (is-subtractive-right-ideal-Semiring R)

module _
  {l1 l2 : Level} (R : Semiring l1) (I : subtractive-right-ideal-Semiring l2 R)
  where

  right-ideal-subtractive-right-ideal-Semiring : right-ideal-Semiring l2 R
  right-ideal-subtractive-right-ideal-Semiring = pr1 I

  is-subtractive-subtractive-right-ideal-Semiring :
    is-subtractive-right-ideal-Semiring R
      right-ideal-subtractive-right-ideal-Semiring
  is-subtractive-subtractive-right-ideal-Semiring =
    pr2 I

  subset-subtractive-right-ideal-Semiring : subset-Semiring l2 R
  subset-subtractive-right-ideal-Semiring =
    subset-right-ideal-Semiring R right-ideal-subtractive-right-ideal-Semiring

  is-right-ideal-subtractive-right-ideal-Semiring :
    is-right-ideal-subset-Semiring R subset-subtractive-right-ideal-Semiring
  is-right-ideal-subtractive-right-ideal-Semiring =
    is-right-ideal-right-ideal-Semiring R
      right-ideal-subtractive-right-ideal-Semiring

  is-in-subtractive-right-ideal-Semiring : type-Semiring R → UU l2
  is-in-subtractive-right-ideal-Semiring =
    is-in-right-ideal-Semiring R right-ideal-subtractive-right-ideal-Semiring

  is-prop-is-in-subtractive-right-ideal-Semiring :
    (x : type-Semiring R) → is-prop (is-in-subtractive-right-ideal-Semiring x)
  is-prop-is-in-subtractive-right-ideal-Semiring =
    is-prop-is-in-right-ideal-Semiring R
      right-ideal-subtractive-right-ideal-Semiring

  type-subtractive-right-ideal-Semiring : UU (l1 ⊔ l2)
  type-subtractive-right-ideal-Semiring =
    type-right-ideal-Semiring R right-ideal-subtractive-right-ideal-Semiring

  inclusion-subtractive-right-ideal-Semiring :
    type-subtractive-right-ideal-Semiring → type-Semiring R
  inclusion-subtractive-right-ideal-Semiring =
    inclusion-right-ideal-Semiring R
      right-ideal-subtractive-right-ideal-Semiring

  ap-inclusion-subtractive-right-ideal-Semiring :
    (x y : type-subtractive-right-ideal-Semiring) → x ＝ y →
    inclusion-subtractive-right-ideal-Semiring x ＝
    inclusion-subtractive-right-ideal-Semiring y
  ap-inclusion-subtractive-right-ideal-Semiring =
    ap-inclusion-right-ideal-Semiring R
      right-ideal-subtractive-right-ideal-Semiring

  is-in-subset-inclusion-subtractive-right-ideal-Semiring :
    (x : type-subtractive-right-ideal-Semiring) →
    is-in-subtractive-right-ideal-Semiring (inclusion-subtractive-right-ideal-Semiring x)
  is-in-subset-inclusion-subtractive-right-ideal-Semiring =
    is-in-subset-inclusion-right-ideal-Semiring R
      right-ideal-subtractive-right-ideal-Semiring

  is-closed-under-eq-subtractive-right-ideal-Semiring :
    {x y : type-Semiring R} → is-in-subtractive-right-ideal-Semiring x →
    (x ＝ y) → is-in-subtractive-right-ideal-Semiring y
  is-closed-under-eq-subtractive-right-ideal-Semiring =
    is-closed-under-eq-right-ideal-Semiring R
      right-ideal-subtractive-right-ideal-Semiring
    
  is-closed-under-eq-subtractive-right-ideal-Semiring' :
    {x y : type-Semiring R} → is-in-subtractive-right-ideal-Semiring y →
    (x ＝ y) → is-in-subtractive-right-ideal-Semiring x
  is-closed-under-eq-subtractive-right-ideal-Semiring' =
    is-closed-under-eq-right-ideal-Semiring' R
      right-ideal-subtractive-right-ideal-Semiring

  is-additive-submonoid-subtractive-right-ideal-Semiring :
    is-additive-submonoid-subset-Semiring R
      subset-subtractive-right-ideal-Semiring
  is-additive-submonoid-subtractive-right-ideal-Semiring =
    is-additive-submonoid-right-ideal-Semiring R
      right-ideal-subtractive-right-ideal-Semiring

  additive-submonoid-subtractive-right-ideal-Semiring :
    Submonoid l2 (additive-monoid-Semiring R)
  additive-submonoid-subtractive-right-ideal-Semiring =
    additive-submonoid-right-ideal-Semiring R
      right-ideal-subtractive-right-ideal-Semiring

  contains-zero-subtractive-right-ideal-Semiring :
    is-in-subtractive-right-ideal-Semiring (zero-Semiring R)
  contains-zero-subtractive-right-ideal-Semiring =
    contains-zero-right-ideal-Semiring R
      right-ideal-subtractive-right-ideal-Semiring

  is-closed-under-addition-subtractive-right-ideal-Semiring :
    is-closed-under-addition-subset-Semiring R
      subset-subtractive-right-ideal-Semiring
  is-closed-under-addition-subtractive-right-ideal-Semiring =
    is-closed-under-addition-right-ideal-Semiring R
      right-ideal-subtractive-right-ideal-Semiring

  is-closed-under-right-multiplication-subtractive-right-ideal-Semiring :
    is-closed-under-right-multiplication-subset-Semiring R
      ( subset-subtractive-right-ideal-Semiring)
  is-closed-under-right-multiplication-subtractive-right-ideal-Semiring =
    is-closed-under-right-multiplication-right-ideal-Semiring R
      right-ideal-subtractive-right-ideal-Semiring

  is-closed-under-multiplication-subtractive-right-ideal-Semiring :
    is-closed-under-multiplication-subset-Semiring R
      ( subset-subtractive-right-ideal-Semiring)
  is-closed-under-multiplication-subtractive-right-ideal-Semiring =
    is-closed-under-multiplication-right-ideal-Semiring R
      right-ideal-subtractive-right-ideal-Semiring

  is-nonunital-subsemiring-subtractive-right-ideal-Semiring :
    is-nonunital-subsemiring-subset-Semiring R subset-subtractive-right-ideal-Semiring
  is-nonunital-subsemiring-subtractive-right-ideal-Semiring =
    is-nonunital-subsemiring-right-ideal-Semiring R
      right-ideal-subtractive-right-ideal-Semiring

  nonunital-subsemiring-subtractive-right-ideal-Semiring :
    Nonunital-Subsemiring l2 R
  nonunital-subsemiring-subtractive-right-ideal-Semiring =
    nonunital-subsemiring-right-ideal-Semiring R
      right-ideal-subtractive-right-ideal-Semiring
```

## Properties

### Characterizing equality of subtractive right ideals in semirings

```agda
module _
  {l1 l2 l3 : Level} (R : Semiring l1) (I : subtractive-right-ideal-Semiring l2 R)
  where

  has-same-elements-subtractive-right-ideal-Semiring :
    (J : subtractive-right-ideal-Semiring l3 R) → UU (l1 ⊔ l2 ⊔ l3)
  has-same-elements-subtractive-right-ideal-Semiring J =
    has-same-elements-subtype
      ( subset-subtractive-right-ideal-Semiring R I)
      ( subset-subtractive-right-ideal-Semiring R J)

module _
  {l1 l2 : Level} (R : Semiring l1) (I : subtractive-right-ideal-Semiring l2 R)
  where

  refl-has-same-elements-subtractive-right-ideal-Semiring :
    has-same-elements-subtractive-right-ideal-Semiring R I I
  refl-has-same-elements-subtractive-right-ideal-Semiring =
    refl-has-same-elements-right-ideal-Semiring R
      (right-ideal-subtractive-right-ideal-Semiring R I)

  is-torsorial-has-same-elements-subtractive-right-ideal-Semiring :
    is-torsorial (has-same-elements-subtractive-right-ideal-Semiring R I)
  is-torsorial-has-same-elements-subtractive-right-ideal-Semiring =
    is-torsorial-Eq-subtype
      ( is-torsorial-has-same-elements-right-ideal-Semiring R
        ( right-ideal-subtractive-right-ideal-Semiring R I))
      ( is-prop-is-subtractive-right-ideal-Semiring R)
      ( right-ideal-subtractive-right-ideal-Semiring R I)
      ( refl-has-same-elements-subtractive-right-ideal-Semiring)
      ( is-subtractive-subtractive-right-ideal-Semiring R I)

  has-same-elements-eq-subtractive-right-ideal-Semiring :
    (J : subtractive-right-ideal-Semiring l2 R) →
    (I ＝ J) → has-same-elements-subtractive-right-ideal-Semiring R I J
  has-same-elements-eq-subtractive-right-ideal-Semiring .I refl =
    refl-has-same-elements-subtractive-right-ideal-Semiring

  is-equiv-has-same-elements-eq-subtractive-right-ideal-Semiring :
    (J : subtractive-right-ideal-Semiring l2 R) →
    is-equiv (has-same-elements-eq-subtractive-right-ideal-Semiring J)
  is-equiv-has-same-elements-eq-subtractive-right-ideal-Semiring =
    fundamental-theorem-id
      is-torsorial-has-same-elements-subtractive-right-ideal-Semiring
      has-same-elements-eq-subtractive-right-ideal-Semiring

  extensionality-subtractive-right-ideal-Semiring :
    (J : subtractive-right-ideal-Semiring l2 R) →
    (I ＝ J) ≃ has-same-elements-subtractive-right-ideal-Semiring R I J
  pr1 (extensionality-subtractive-right-ideal-Semiring J) =
    has-same-elements-eq-subtractive-right-ideal-Semiring J
  pr2 (extensionality-subtractive-right-ideal-Semiring J) =
    is-equiv-has-same-elements-eq-subtractive-right-ideal-Semiring J

  eq-has-same-elements-subtractive-right-ideal-Semiring :
    (J : subtractive-right-ideal-Semiring l2 R) →
    has-same-elements-subtractive-right-ideal-Semiring R I J → I ＝ J
  eq-has-same-elements-subtractive-right-ideal-Semiring J =
    map-inv-equiv (extensionality-subtractive-right-ideal-Semiring J)
```

