# Multiplicative inverses of complex numbers

```agda
module complex-numbers.multiplicative-inverses-nonzero-complex-numbers where
```

<details><summary>Imports</summary>

```agda
open import complex-numbers.complex-numbers
open import complex-numbers.conjugation-complex-numbers
open import complex-numbers.magnitude-complex-numbers
open import complex-numbers.multiplication-complex-numbers
open import complex-numbers.nonzero-complex-numbers
open import complex-numbers.similarity-complex-numbers

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import real-numbers.multiplication-real-numbers
open import real-numbers.multiplicative-inverses-positive-real-numbers
open import real-numbers.rational-real-numbers
```

</details>

## Idea

[Nonzero](complex-numbers.nonzero-complex-numbers.md)
[complex numbers](complex-numbers.complex-numbers.md) have inverses under
[multiplication](complex-numbers.multiplication-complex-numbers.md).

## Definition

```agda
complex-inv-nonzero-ℂ : {l : Level} (z : nonzero-ℂ l) → ℂ l
complex-inv-nonzero-ℂ (z , z≠0) =
  conjugate-ℂ z *ℂ
  complex-ℝ (real-inv-ℝ⁺ (positive-squared-magnitude-nonzero-ℂ (z , z≠0)))
```

## Properties

### Inverse laws of multiplication

```agda
abstract
  left-inverse-law-mul-ℂ : {l : Level} (z : nonzero-ℂ l) →
    sim-ℂ (complex-nonzero-ℂ z *ℂ complex-inv-nonzero-ℂ z) one-ℂ
  left-inverse-law-mul-ℂ (z@(a +iℂ b) , z≠0) =
    similarity-reasoning-ℂ
      z *ℂ
      ( conjugate-ℂ z *ℂ
        complex-ℝ
          ( real-inv-ℝ⁺ (positive-squared-magnitude-nonzero-ℂ (z , z≠0))))
      ~ℂ
        ( z *ℂ conjugate-ℂ z) *ℂ
        ( complex-ℝ
          ( real-inv-ℝ⁺ (positive-squared-magnitude-nonzero-ℂ (z , z≠0))))
        by sim-eq-ℂ (inv (associative-mul-ℂ _ _ _))
      ~ℂ
        complex-ℝ (squared-magnitude-ℂ z) *ℂ
        complex-ℝ
          ( real-inv-ℝ⁺ (positive-squared-magnitude-nonzero-ℂ (z , z≠0)))
        by sim-eq-ℂ (ap-mul-ℂ (eq-squared-magnitude-mul-conjugate-ℂ z) refl)
      ~ℂ
        complex-ℝ
          ( squared-magnitude-ℂ z *ℝ
            real-inv-ℝ⁺ (positive-squared-magnitude-nonzero-ℂ (z , z≠0)))
        by sim-eq-ℂ (mul-complex-ℝ _ _)
      ~ℂ complex-ℝ one-ℝ
        by
          preserves-sim-complex-ℝ
            ( right-inverse-law-mul-ℝ⁺
              ( positive-squared-magnitude-nonzero-ℂ (z , z≠0)))
      ~ℂ one-ℂ
        by sim-eq-ℂ eq-complex-one-ℝ

  right-inverse-law-mul-ℂ : {l : Level} (z : nonzero-ℂ l) →
    sim-ℂ (complex-inv-nonzero-ℂ z *ℂ complex-nonzero-ℂ z) one-ℂ
  right-inverse-law-mul-ℂ z =
    tr (λ w → sim-ℂ w one-ℂ) (commutative-mul-ℂ _ _) (left-inverse-law-mul-ℂ z)
```
