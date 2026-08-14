# Subtractive left ideals of semirings

```agda
module ring-theory.subtractive-left-ideals-semirings where
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

open import ring-theory.left-ideals-semirings
open import ring-theory.nonunital-subsemirings
open import ring-theory.semirings
open import ring-theory.subsets-semirings
open import ring-theory.subtractive-subsets-semirings
```

</details>

## Idea

A [left ideal](ring-theory.left-ideals-semirings.md) `I` of a [semiring](ring-theory.semirings.md) `R` is said to be
{{#concept "subtractive" Disambiguation="left ideal of a semiring" Agda=subtractive-left-ideal-Semiring}}
if for any `x y ∈ R` we have

```text
  x ∈ I ⇒ x + y ∈ I ⇒ y ∈ I.
```

That is, a subtractive left ideal is a left ideal satisfying a 3-for-2 property.

## Definitions

### The predicate of being a subtractive left ideal

```agda
module _
  {l1 l2 : Level} (R : Semiring l1) (I : left-ideal-Semiring l2 R)
  where

  is-subtractive-left-ideal-Semiring :
    UU (l1 ⊔ l2)
  is-subtractive-left-ideal-Semiring =
    is-subtractive-subset-Semiring R (subset-left-ideal-Semiring R I)

  is-prop-is-subtractive-left-ideal-Semiring :
    is-prop is-subtractive-left-ideal-Semiring
  is-prop-is-subtractive-left-ideal-Semiring =
    is-prop-is-subtractive-subset-Semiring R (subset-left-ideal-Semiring R I)

  is-subtractive-prop-left-ideal-Semiring :
    Prop (l1 ⊔ l2)
  pr1 is-subtractive-prop-left-ideal-Semiring =
    is-subtractive-left-ideal-Semiring
  pr2 is-subtractive-prop-left-ideal-Semiring =
    is-prop-is-subtractive-left-ideal-Semiring
```

### The type of subtractive left ideals

```agda
subtractive-left-ideal-Semiring :
  {l1 : Level} (l2 : Level) (R : Semiring l1) → UU (l1 ⊔ lsuc l2)
subtractive-left-ideal-Semiring l2 R =
  Σ (left-ideal-Semiring l2 R) (is-subtractive-left-ideal-Semiring R)

module _
  {l1 l2 : Level} (R : Semiring l1) (I : subtractive-left-ideal-Semiring l2 R)
  where

  left-ideal-subtractive-left-ideal-Semiring : left-ideal-Semiring l2 R
  left-ideal-subtractive-left-ideal-Semiring = pr1 I

  is-subtractive-subtractive-left-ideal-Semiring :
    is-subtractive-left-ideal-Semiring R
      left-ideal-subtractive-left-ideal-Semiring
  is-subtractive-subtractive-left-ideal-Semiring =
    pr2 I

  subset-subtractive-left-ideal-Semiring : subset-Semiring l2 R
  subset-subtractive-left-ideal-Semiring =
    subset-left-ideal-Semiring R left-ideal-subtractive-left-ideal-Semiring

  is-left-ideal-subtractive-left-ideal-Semiring :
    is-left-ideal-subset-Semiring R subset-subtractive-left-ideal-Semiring
  is-left-ideal-subtractive-left-ideal-Semiring =
    is-left-ideal-left-ideal-Semiring R
      left-ideal-subtractive-left-ideal-Semiring

  is-in-subtractive-left-ideal-Semiring : type-Semiring R → UU l2
  is-in-subtractive-left-ideal-Semiring =
    is-in-left-ideal-Semiring R left-ideal-subtractive-left-ideal-Semiring

  is-prop-is-in-subtractive-left-ideal-Semiring :
    (x : type-Semiring R) → is-prop (is-in-subtractive-left-ideal-Semiring x)
  is-prop-is-in-subtractive-left-ideal-Semiring =
    is-prop-is-in-left-ideal-Semiring R
      left-ideal-subtractive-left-ideal-Semiring

  type-subtractive-left-ideal-Semiring : UU (l1 ⊔ l2)
  type-subtractive-left-ideal-Semiring =
    type-left-ideal-Semiring R left-ideal-subtractive-left-ideal-Semiring

  inclusion-subtractive-left-ideal-Semiring :
    type-subtractive-left-ideal-Semiring → type-Semiring R
  inclusion-subtractive-left-ideal-Semiring =
    inclusion-left-ideal-Semiring R
      left-ideal-subtractive-left-ideal-Semiring

  ap-inclusion-subtractive-left-ideal-Semiring :
    (x y : type-subtractive-left-ideal-Semiring) → x ＝ y →
    inclusion-subtractive-left-ideal-Semiring x ＝
    inclusion-subtractive-left-ideal-Semiring y
  ap-inclusion-subtractive-left-ideal-Semiring =
    ap-inclusion-left-ideal-Semiring R
      left-ideal-subtractive-left-ideal-Semiring

  is-in-subset-inclusion-subtractive-left-ideal-Semiring :
    (x : type-subtractive-left-ideal-Semiring) →
    is-in-subtractive-left-ideal-Semiring (inclusion-subtractive-left-ideal-Semiring x)
  is-in-subset-inclusion-subtractive-left-ideal-Semiring =
    is-in-subset-inclusion-left-ideal-Semiring R
      left-ideal-subtractive-left-ideal-Semiring

  is-closed-under-eq-subtractive-left-ideal-Semiring :
    {x y : type-Semiring R} → is-in-subtractive-left-ideal-Semiring x →
    (x ＝ y) → is-in-subtractive-left-ideal-Semiring y
  is-closed-under-eq-subtractive-left-ideal-Semiring =
    is-closed-under-eq-left-ideal-Semiring R
      left-ideal-subtractive-left-ideal-Semiring
    
  is-closed-under-eq-subtractive-left-ideal-Semiring' :
    {x y : type-Semiring R} → is-in-subtractive-left-ideal-Semiring y →
    (x ＝ y) → is-in-subtractive-left-ideal-Semiring x
  is-closed-under-eq-subtractive-left-ideal-Semiring' =
    is-closed-under-eq-left-ideal-Semiring' R
      left-ideal-subtractive-left-ideal-Semiring

  is-additive-submonoid-subtractive-left-ideal-Semiring :
    is-additive-submonoid-subset-Semiring R
      subset-subtractive-left-ideal-Semiring
  is-additive-submonoid-subtractive-left-ideal-Semiring =
    is-additive-submonoid-left-ideal-Semiring R
      left-ideal-subtractive-left-ideal-Semiring

  additive-submonoid-subtractive-left-ideal-Semiring :
    Submonoid l2 (additive-monoid-Semiring R)
  additive-submonoid-subtractive-left-ideal-Semiring =
    additive-submonoid-left-ideal-Semiring R
      left-ideal-subtractive-left-ideal-Semiring

  contains-zero-subtractive-left-ideal-Semiring :
    is-in-subtractive-left-ideal-Semiring (zero-Semiring R)
  contains-zero-subtractive-left-ideal-Semiring =
    contains-zero-left-ideal-Semiring R
      left-ideal-subtractive-left-ideal-Semiring

  is-closed-under-addition-subtractive-left-ideal-Semiring :
    is-closed-under-addition-subset-Semiring R
      subset-subtractive-left-ideal-Semiring
  is-closed-under-addition-subtractive-left-ideal-Semiring =
    is-closed-under-addition-left-ideal-Semiring R
      left-ideal-subtractive-left-ideal-Semiring

  is-closed-under-left-multiplication-subtractive-left-ideal-Semiring :
    is-closed-under-left-multiplication-subset-Semiring R
      ( subset-subtractive-left-ideal-Semiring)
  is-closed-under-left-multiplication-subtractive-left-ideal-Semiring =
    is-closed-under-left-multiplication-left-ideal-Semiring R
      left-ideal-subtractive-left-ideal-Semiring

  is-closed-under-multiplication-subtractive-left-ideal-Semiring :
    is-closed-under-multiplication-subset-Semiring R
      ( subset-subtractive-left-ideal-Semiring)
  is-closed-under-multiplication-subtractive-left-ideal-Semiring =
    is-closed-under-multiplication-left-ideal-Semiring R
      left-ideal-subtractive-left-ideal-Semiring

  is-nonunital-subsemiring-subtractive-left-ideal-Semiring :
    is-nonunital-subsemiring-subset-Semiring R subset-subtractive-left-ideal-Semiring
  is-nonunital-subsemiring-subtractive-left-ideal-Semiring =
    is-nonunital-subsemiring-left-ideal-Semiring R
      left-ideal-subtractive-left-ideal-Semiring

  nonunital-subsemiring-subtractive-left-ideal-Semiring :
    Nonunital-Subsemiring l2 R
  nonunital-subsemiring-subtractive-left-ideal-Semiring =
    nonunital-subsemiring-left-ideal-Semiring R
      left-ideal-subtractive-left-ideal-Semiring
```

## Properties

### Characterizing equality of subtractive left ideals in semirings

```agda
module _
  {l1 l2 l3 : Level} (R : Semiring l1) (I : subtractive-left-ideal-Semiring l2 R)
  where

  has-same-elements-subtractive-left-ideal-Semiring :
    (J : subtractive-left-ideal-Semiring l3 R) → UU (l1 ⊔ l2 ⊔ l3)
  has-same-elements-subtractive-left-ideal-Semiring J =
    has-same-elements-subtype
      ( subset-subtractive-left-ideal-Semiring R I)
      ( subset-subtractive-left-ideal-Semiring R J)

module _
  {l1 l2 : Level} (R : Semiring l1) (I : subtractive-left-ideal-Semiring l2 R)
  where

  refl-has-same-elements-subtractive-left-ideal-Semiring :
    has-same-elements-subtractive-left-ideal-Semiring R I I
  refl-has-same-elements-subtractive-left-ideal-Semiring =
    refl-has-same-elements-left-ideal-Semiring R
      (left-ideal-subtractive-left-ideal-Semiring R I)

  is-torsorial-has-same-elements-subtractive-left-ideal-Semiring :
    is-torsorial (has-same-elements-subtractive-left-ideal-Semiring R I)
  is-torsorial-has-same-elements-subtractive-left-ideal-Semiring =
    is-torsorial-Eq-subtype
      ( is-torsorial-has-same-elements-left-ideal-Semiring R
        ( left-ideal-subtractive-left-ideal-Semiring R I))
      ( is-prop-is-subtractive-left-ideal-Semiring R)
      ( left-ideal-subtractive-left-ideal-Semiring R I)
      ( refl-has-same-elements-subtractive-left-ideal-Semiring)
      ( is-subtractive-subtractive-left-ideal-Semiring R I)

  has-same-elements-eq-subtractive-left-ideal-Semiring :
    (J : subtractive-left-ideal-Semiring l2 R) →
    (I ＝ J) → has-same-elements-subtractive-left-ideal-Semiring R I J
  has-same-elements-eq-subtractive-left-ideal-Semiring .I refl =
    refl-has-same-elements-subtractive-left-ideal-Semiring

  is-equiv-has-same-elements-eq-subtractive-left-ideal-Semiring :
    (J : subtractive-left-ideal-Semiring l2 R) →
    is-equiv (has-same-elements-eq-subtractive-left-ideal-Semiring J)
  is-equiv-has-same-elements-eq-subtractive-left-ideal-Semiring =
    fundamental-theorem-id
      is-torsorial-has-same-elements-subtractive-left-ideal-Semiring
      has-same-elements-eq-subtractive-left-ideal-Semiring

  extensionality-subtractive-left-ideal-Semiring :
    (J : subtractive-left-ideal-Semiring l2 R) →
    (I ＝ J) ≃ has-same-elements-subtractive-left-ideal-Semiring R I J
  pr1 (extensionality-subtractive-left-ideal-Semiring J) =
    has-same-elements-eq-subtractive-left-ideal-Semiring J
  pr2 (extensionality-subtractive-left-ideal-Semiring J) =
    is-equiv-has-same-elements-eq-subtractive-left-ideal-Semiring J

  eq-has-same-elements-subtractive-left-ideal-Semiring :
    (J : subtractive-left-ideal-Semiring l2 R) →
    has-same-elements-subtractive-left-ideal-Semiring R I J → I ＝ J
  eq-has-same-elements-subtractive-left-ideal-Semiring J =
    map-inv-equiv (extensionality-subtractive-left-ideal-Semiring J)
```

