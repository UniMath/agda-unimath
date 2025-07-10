# The field of rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.field-of-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.discrete-fields

open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.additive-group-of-rational-numbers
open import elementary-number-theory.greatest-common-divisor-integers
open import elementary-number-theory.integer-fractions
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integer-fractions
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.multiplicative-group-of-positive-rational-numbers
open import elementary-number-theory.multiplicative-group-of-rational-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonzero-integers
open import elementary-number-theory.nonzero-rational-numbers
open import elementary-number-theory.positive-integers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.reduced-integer-fractions
open import elementary-number-theory.relatively-prime-integers
open import elementary-number-theory.ring-of-integers
open import elementary-number-theory.ring-of-rational-numbers
open import elementary-number-theory.unit-fractions-rational-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.images
open import foundation.iterating-automorphisms
open import foundation.reflecting-maps-equivalence-relations
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.contractible-maps
open import foundation-core.contractible-types
open import foundation-core.coproduct-types
open import foundation-core.empty-types
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.retractions
open import foundation-core.sections
open import foundation-core.sets
open import foundation-core.subtypes
open import foundation-core.transport-along-identifications

open import group-theory.cores-monoids
open import group-theory.groups
open import group-theory.invertible-elements-monoids

open import ring-theory.division-rings
open import ring-theory.groups-of-units-rings
open import ring-theory.homomorphisms-rings
open import ring-theory.initial-rings
open import ring-theory.invertible-elements-rings
open import ring-theory.localizations-rings
open import ring-theory.rings
open import ring-theory.semirings
```

</details>

## Idea

The type of [rational numbers](elementary-number-theory.rational-numbers.md)
equipped with [addition](elementary-number-theory.addition-rational-numbers.md)
and
[multiplication](elementary-number-theory.multiplication-rational-numbers.md) is
a [discrete field](commutative-algebra.discrete-fields.md), i.e., a
[commutative ring](commutative-algebra.commutative-rings.md) whose
[nonzero](elementary-number-theory.nonzero-rational-numbers.md) elements are
[invertible](ring-theory.invertible-elements-rings.md).

## Definitions

### The ring of rational numbers is a division ring

```agda
is-division-ring-ℚ : is-division-Ring ring-ℚ
pr1 is-division-ring-ℚ = is-nonzero-one-ℚ ∘ inv
pr2 is-division-ring-ℚ x H = is-invertible-element-ring-is-nonzero-ℚ x (H ∘ inv)
```

### The rational numbers form a discrete field

```agda
is-discrete-field-ℚ : is-discrete-field-Commutative-Ring commutative-ring-ℚ
is-discrete-field-ℚ = is-division-ring-ℚ
```

## Properties

### The ring of rational numbers is the [localization](ring-theory.localizations-rings.md) of the ring of [integers](elementary-number-theory.ring-of-integers.md) at the set of [positive integers](elementary-number-theory.positive-integers.md)

```agda
inverts-positive-integers-ℚ :
  inverts-subset-hom-Ring ℤ-Ring ring-ℚ subtype-positive-ℤ
  ( initial-hom-Ring ring-ℚ)
inverts-positive-integers-ℚ (inr (inr x)) star =
  is-invertible-element-ring-is-nonzero-ℚ (pr1 (pr1 (initial-hom-Ring ring-ℚ))
  ( inr (inr x))) lem where
  lem : is-nonzero-ℚ (pr1 (pr1 (initial-hom-Ring ring-ℚ)) (inr (inr x)))
  lem =
    is-nonzero-is-nonzero-numerator-ℚ (pr1 (pr1 (initial-hom-Ring ring-ℚ))
    ( inr (inr x))) {!   !}

inverts-positive-integers-hom-ℚ :
  {l : Level} (R : Ring l) → inverts-subset-hom-Ring ℤ-Ring R subtype-positive-ℤ
  ( initial-hom-Ring R) → hom-Ring ring-ℚ R
pr1 (pr1 (inverts-positive-integers-hom-ℚ R R-inv)) ((x , y , y>0) , _) =
  mul-Ring R (map-hom-Ring ℤ-Ring R (initial-hom-Ring R) x)
  ( inv-is-invertible-element-Ring R (R-inv y y>0))
pr2 (pr1 (inverts-positive-integers-hom-ℚ R R-inv))
  {(x , y , y>0) , xy-red} {(z , w , w>0) , zw-red} =
    {!   !}
pr1 (pr2 (inverts-positive-integers-hom-ℚ R R-inv))
  {(x , y , y>0) , xy-red} {(z , w , w>0) , zw-red} =
    {!   !}
pr2 (pr2 (inverts-positive-integers-hom-ℚ R R-inv)) = pr1
  (pr2
    (R-inv
      (pr1
        (pr1
          (pr1
            (pr2
              (multiplicative-monoid-Semiring
                (semiring-Ring ring-ℚ))))))
    star))

universal-property-ℚ-ℤ :
  (l : Level) → universal-property-localization-subset-Ring l ℤ-Ring ring-ℚ
  subtype-positive-ℤ (initial-hom-Ring ring-ℚ) inverts-positive-integers-ℚ
pr1 (pr1 (universal-property-ℚ-ℤ l R)) (f , f-inv) =
  inverts-positive-integers-hom-ℚ R lem where
  lem : inverts-subset-hom-Ring ℤ-Ring R subtype-positive-ℤ (initial-hom-Ring R)
  lem =
    tr (inverts-subset-hom-Ring ℤ-Ring R subtype-positive-ℤ)
    ( inv (contraction-initial-hom-Ring R f)) f-inv
pr2 (pr1 (universal-property-ℚ-ℤ l R)) (f , f-inv) =
  eq-type-subtype (inverts-subset-hom-ring-Prop ℤ-Ring R subtype-positive-ℤ)
  ( inv (contraction-initial-hom-Ring R (pr1
  ((precomp-universal-property-localization-subset-Ring ℤ-Ring ring-ℚ
    R subtype-positive-ℤ (initial-hom-Ring ring-ℚ)
    inverts-positive-integers-ℚ
    ∘ pr1 (pr1 (universal-property-ℚ-ℤ l R)))
    (f , f-inv))))) ∙ eq-type-subtype
    ( inverts-subset-hom-ring-Prop ℤ-Ring R subtype-positive-ℤ)
    ( contraction-initial-hom-Ring R f)
pr1 (pr2 (universal-property-ℚ-ℤ l R)) (f , f-inv) =
  inverts-positive-integers-hom-ℚ R lem where
  lem : inverts-subset-hom-Ring ℤ-Ring R subtype-positive-ℤ (initial-hom-Ring R)
  lem =
    tr (inverts-subset-hom-Ring ℤ-Ring R subtype-positive-ℤ)
    ( inv (contraction-initial-hom-Ring R f)) f-inv
pr2 (pr2 (universal-property-ℚ-ℤ l R)) f =
  eq-htpy-hom-Ring ring-ℚ R ((pr1 (pr2 (universal-property-ℚ-ℤ l R)) ∘
    precomp-universal-property-localization-subset-Ring ℤ-Ring ring-ℚ R
    subtype-positive-ℤ (initial-hom-Ring ring-ℚ)
    inverts-positive-integers-ℚ)
    f) f htpy where
  htpy :
    htpy-hom-Ring ring-ℚ R ((pr1 (pr2 (universal-property-ℚ-ℤ l R)) ∘
    precomp-universal-property-localization-subset-Ring ℤ-Ring ring-ℚ R
    subtype-positive-ℤ
    (initial-hom-Ring ring-ℚ) inverts-positive-integers-ℚ) f) f
  htpy ((x , y , y>0) , _) = {!   !}
```
