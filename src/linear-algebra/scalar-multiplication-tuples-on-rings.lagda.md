# Scalar multiplication of tuples on rings

```agda
module linear-algebra.scalar-multiplication-tuples-on-rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.endomorphism-rings-abelian-groups
open import group-theory.homomorphisms-abelian-groups

open import linear-algebra.left-modules-rings
open import linear-algebra.tuples-on-rings

open import lists.tuples

open import ring-theory.homomorphisms-rings
open import ring-theory.rings
```

</details>

## Definition

For [tuples on rings](linear-algebra.tuples-on-rings.md),
{{#concept "scalar multiplication" disambiguation="Of tuples on rings" WD="scalar multiplication" WDID=Q126736}}
is an operation taking an element `c` of a [ring](ring-theory.rings.md) and a
tuple of elements of that ring and multiplying each element of the tuple by `c`.
With addition of tuples on rings, this forms a
[left module](linear-algebra.left-modules-rings.md).

### Scalar multiplication of tuples on rings

```agda
module _
  {l : Level} (R : Ring l)
  where

  scalar-mul-tuple-Ring :
    {n : ℕ} (r : type-Ring R) → tuple-Ring R n → tuple-Ring R n
  scalar-mul-tuple-Ring r empty-tuple = empty-tuple
  scalar-mul-tuple-Ring r (x ∷ v) = mul-Ring R r x ∷ scalar-mul-tuple-Ring r v

  associative-scalar-mul-tuple-Ring :
    {n : ℕ} (r s : type-Ring R) (v : tuple-Ring R n) →
    scalar-mul-tuple-Ring (mul-Ring R r s) v ＝
    scalar-mul-tuple-Ring r (scalar-mul-tuple-Ring s v)
  associative-scalar-mul-tuple-Ring r s empty-tuple = refl
  associative-scalar-mul-tuple-Ring r s (x ∷ v) =
    ap-binary _∷_
      ( associative-mul-Ring R r s x)
      ( associative-scalar-mul-tuple-Ring r s v)

  unit-law-scalar-mul-tuple-Ring :
    {n : ℕ} (v : tuple-Ring R n) → scalar-mul-tuple-Ring (one-Ring R) v ＝ v
  unit-law-scalar-mul-tuple-Ring empty-tuple = refl
  unit-law-scalar-mul-tuple-Ring (x ∷ v) =
    ap-binary _∷_
      ( left-unit-law-mul-Ring R x)
      ( unit-law-scalar-mul-tuple-Ring v)

  left-distributive-scalar-mul-add-tuple-Ring :
    {n : ℕ} (r : type-Ring R) (v1 v2 : tuple-Ring R n) →
    scalar-mul-tuple-Ring r (add-tuple-Ring R v1 v2) ＝
    add-tuple-Ring R (scalar-mul-tuple-Ring r v1) (scalar-mul-tuple-Ring r v2)
  left-distributive-scalar-mul-add-tuple-Ring r empty-tuple empty-tuple = refl
  left-distributive-scalar-mul-add-tuple-Ring r (x ∷ v1) (y ∷ v2) =
    ap-binary _∷_
      ( left-distributive-mul-add-Ring R r x y)
      ( left-distributive-scalar-mul-add-tuple-Ring r v1 v2)

  right-distributive-scalar-mul-add-tuple-Ring :
    {n : ℕ} (r s : type-Ring R) (v : tuple-Ring R n) →
    scalar-mul-tuple-Ring (add-Ring R r s) v ＝
    add-tuple-Ring R (scalar-mul-tuple-Ring r v) (scalar-mul-tuple-Ring s v)
  right-distributive-scalar-mul-add-tuple-Ring r s empty-tuple = refl
  right-distributive-scalar-mul-add-tuple-Ring r s (x ∷ v) =
    ap-binary _∷_
      ( right-distributive-mul-add-Ring R r s x)
      ( right-distributive-scalar-mul-add-tuple-Ring r s v)
```

## Properties

### Scalar multiplication defines an `Ab`-endomorphism of `tuple-Ring`s, and this mapping is a ring homomorphism `R → End(tuple R n)`

```agda
  endo-scalar-mul-tuple-Ring :
    (n : ℕ) (r : type-Ring R) → hom-Ab (tuple-Ring-Ab R n) (tuple-Ring-Ab R n)
  pr1 (endo-scalar-mul-tuple-Ring n r) = scalar-mul-tuple-Ring r
  pr2 (endo-scalar-mul-tuple-Ring n r) {x} {y} =
    left-distributive-scalar-mul-add-tuple-Ring r x y

  scalar-mul-hom-Ring :
    (n : ℕ) → hom-Ring R (endomorphism-ring-Ab (tuple-Ring-Ab R n))
  pr1 (pr1 (scalar-mul-hom-Ring n)) = endo-scalar-mul-tuple-Ring n
  pr2 (pr1 (scalar-mul-hom-Ring n)) {k1} {k2} =
    eq-htpy-hom-Ab
      ( tuple-Ring-Ab R n)
      ( tuple-Ring-Ab R n)
      ( right-distributive-scalar-mul-add-tuple-Ring k1 k2)
  pr1 (pr2 (scalar-mul-hom-Ring n)) {k1} {k2} =
    eq-htpy-hom-Ab
      ( tuple-Ring-Ab R n)
      ( tuple-Ring-Ab R n)
      ( associative-scalar-mul-tuple-Ring k1 k2)
  pr2 (pr2 (scalar-mul-hom-Ring n)) =
    eq-htpy-hom-Ab
      ( tuple-Ring-Ab R n)
      ( tuple-Ring-Ab R n)
      ( unit-law-scalar-mul-tuple-Ring)

  tuple-left-module-Ring : (n : ℕ) → left-module-Ring l R
  tuple-left-module-Ring n = tuple-Ring-Ab R n , scalar-mul-hom-Ring n
```
