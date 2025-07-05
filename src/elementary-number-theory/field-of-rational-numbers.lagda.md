# The field of rational numbers

```agda
module elementary-number-theory.field-of-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.discrete-fields

open import elementary-number-theory.greatest-common-divisor-integers
open import elementary-number-theory.integer-fractions
open import elementary-number-theory.integers
open import elementary-number-theory.multiplicative-group-of-rational-numbers
open import elementary-number-theory.nonzero-rational-numbers
open import elementary-number-theory.ring-of-rational-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonzero-integers
open import elementary-number-theory.positive-integers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.reduced-integer-fractions
open import elementary-number-theory.relatively-prime-integers
open import elementary-number-theory.ring-of-integers
open import elementary-number-theory.unit-fractions-rational-numbers

open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.images
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

open import group-theory.invertible-elements-monoids

open import ring-theory.division-rings
open import ring-theory.homomorphisms-rings
open import ring-theory.invertible-elements-rings
open import ring-theory.localizations-rings
open import ring-theory.rings
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

### The ring of rational numbers is the [localization](ring-theory.localizations-rings.md) of the ring of [integers](elementary-number-theory.ring-of-integers.md) at the set of [nonzero integers](elementary-number-theory.nonzero-integers.md)

```agda
inverts-nonzero-integers-ℚ : inverts-subset-hom-Ring ℤ-Ring ring-ℚ is-nonzero-prop-ℤ (initial-hom-Ring ring-ℚ)
pr1 (inverts-nonzero-integers-ℚ (inl x) x≠0) = reciprocal-rational-succ-ℕ x
pr2 (inverts-nonzero-integers-ℚ (inl x) x≠0) = {!   !}
inverts-nonzero-integers-ℚ (inr (inl star)) 0≠0 = ex-falso (0≠0 refl)
pr1 (inverts-nonzero-integers-ℚ (inr (inr x)) x≠0) = neg-ℚ (reciprocal-rational-succ-ℕ x)
pr2 (inverts-nonzero-integers-ℚ (inr (inr x)) x≠0) = {!   !}

universal-property-ℚ-ℤ : (l : Level) → universal-property-localization-subset-Ring l ℤ-Ring ring-ℚ is-nonzero-prop-ℤ (initial-hom-Ring ring-ℚ) inverts-nonzero-integers-ℚ
pr1 (pr1 (universal-property-ℚ-ℤ l R)) = {!   !}
pr2 (pr1 (universal-property-ℚ-ℤ l R)) = {!   !}
pr1 (pr2 (universal-property-ℚ-ℤ l R)) = {!   !}
pr2 (pr2 (universal-property-ℚ-ℤ l R)) = {!   !}
```
