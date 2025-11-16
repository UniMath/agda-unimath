# Multiplicative inverses of complex numbers

```agda
module complex-numbers.multiplicative-inverses-nonzero-complex-numbers where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.invertible-elements-commutative-rings

open import complex-numbers.complex-numbers
open import complex-numbers.conjugation-complex-numbers
open import complex-numbers.large-ring-of-complex-numbers
open import complex-numbers.magnitude-complex-numbers
open import complex-numbers.multiplication-complex-numbers
open import complex-numbers.nonzero-complex-numbers
open import complex-numbers.raising-universe-levels-complex-numbers
open import complex-numbers.similarity-complex-numbers

open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.empty-types
open import foundation.function-types
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

open import real-numbers.multiplication-nonzero-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.multiplicative-inverses-positive-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.nonzero-real-numbers
open import real-numbers.positive-and-negative-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-real-numbers
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
  right-inverse-law-mul-nonzero-ℂ : {l : Level} (z : nonzero-ℂ l) →
    sim-ℂ (complex-nonzero-ℂ z *ℂ complex-inv-nonzero-ℂ z) one-ℂ
  right-inverse-law-mul-nonzero-ℂ (z@(a +iℂ b) , z≠0) =
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

  left-inverse-law-mul-nonzero-ℂ : {l : Level} (z : nonzero-ℂ l) →
    sim-ℂ (complex-inv-nonzero-ℂ z *ℂ complex-nonzero-ℂ z) one-ℂ
  left-inverse-law-mul-nonzero-ℂ z =
    tr
      ( λ w → sim-ℂ w one-ℂ)
      ( commutative-mul-ℂ _ _)
      ( right-inverse-law-mul-nonzero-ℂ z)
```

### If a complex number has a multiplicative inverse, it is nonzero

```agda
abstract
  is-nonzero-has-right-inverse-mul-ℂ :
    {l1 l2 : Level} (z : ℂ l1) (w : ℂ l2) → sim-ℂ (z *ℂ w) one-ℂ →
    is-nonzero-ℂ z
  is-nonzero-has-right-inverse-mul-ℂ z w zw=1 =
    is-nonzero-is-positive-magnitude-ℂ
      ( z)
      ( elim-disjunction
        ( is-positive-prop-ℝ ∥ z ∥ℂ)
        ( λ |z|<0 →
          ex-falso
            ( is-not-negative-and-nonnegative-ℝ
              ( |z|<0 , is-nonnegative-real-ℝ⁰⁺ (nonnegative-magnitude-ℂ z))))
        ( id)
        ( pr1
          ( is-nonzero-factors-is-nonzero-mul-ℝ
            ( ∥ z ∥ℂ)
            ( ∥ w ∥ℂ)
            ( is-nonzero-sim-ℝ
              ( symmetric-sim-ℝ
                ( similarity-reasoning-ℝ
                  ∥ z ∥ℂ *ℝ ∥ w ∥ℂ
                  ~ℝ ∥ z *ℂ w ∥ℂ
                    by sim-eq-ℝ (inv (distributive-magnitude-mul-ℂ z w))
                  ~ℝ ∥ one-ℂ ∥ℂ
                    by preserves-sim-magnitude-ℂ zw=1
                  ~ℝ one-ℝ
                    by sim-eq-ℝ magnitude-one-ℂ))
              ( is-nonzero-is-positive-ℝ is-positive-one-ℝ)))))

  is-nonzero-has-left-inverse-mul-ℂ :
    {l1 l2 : Level} (z : ℂ l1) (w : ℂ l2) → sim-ℂ (z *ℂ w) one-ℂ →
    is-nonzero-ℂ w
  is-nonzero-has-left-inverse-mul-ℂ z w zw=1 =
    is-nonzero-has-right-inverse-mul-ℂ
      ( w)
      ( z)
      ( tr (λ x → sim-ℂ x one-ℂ) (commutative-mul-ℂ z w) zw=1)
```

### The multiplicative inverse of a nonzero complex number is nonzero

```agda
abstract
  is-nonzero-complex-inv-nonzero-ℂ :
    {l : Level} (z : nonzero-ℂ l) → is-nonzero-ℂ (complex-inv-nonzero-ℂ z)
  is-nonzero-complex-inv-nonzero-ℂ z =
    is-nonzero-has-left-inverse-mul-ℂ
      ( _)
      ( _)
      ( right-inverse-law-mul-nonzero-ℂ z)

inv-nonzero-ℂ : {l : Level} → nonzero-ℂ l → nonzero-ℂ l
inv-nonzero-ℂ z = (complex-inv-nonzero-ℂ z , is-nonzero-complex-inv-nonzero-ℂ z)
```

### A complex number is invertible if and only if it is nonzero

```agda
abstract
  is-nonzero-is-invertible-ℂ :
    {l : Level} (z : ℂ l) →
    is-invertible-element-Commutative-Ring (commutative-ring-ℂ l) z →
    is-nonzero-ℂ z
  is-nonzero-is-invertible-ℂ z (w , zw=1 , _) =
    is-nonzero-has-right-inverse-mul-ℂ
      ( z)
      ( w)
      ( transitive-sim-ℂ _ _ _
        ( symmetric-sim-ℂ (sim-raise-ℂ _ one-ℂ))
        ( sim-eq-ℂ zw=1))

  is-invertible-is-nonzero-ℂ :
    {l : Level} (z : ℂ l) → is-nonzero-ℂ z →
    is-invertible-element-Commutative-Ring (commutative-ring-ℂ l) z
  is-invertible-is-nonzero-ℂ z z≠0 =
    ( complex-inv-nonzero-ℂ (z , z≠0) ,
      eq-sim-ℂ
        ( similarity-reasoning-ℂ
          z *ℂ complex-inv-nonzero-ℂ (z , z≠0)
          ~ℂ one-ℂ
            by right-inverse-law-mul-nonzero-ℂ (z , z≠0)
          ~ℂ raise-ℂ _ one-ℂ
            by sim-raise-ℂ _ one-ℂ) ,
      eq-sim-ℂ
        ( similarity-reasoning-ℂ
          complex-inv-nonzero-ℂ (z , z≠0) *ℂ z
          ~ℂ one-ℂ
            by left-inverse-law-mul-nonzero-ℂ (z , z≠0)
          ~ℂ raise-ℂ _ one-ℂ
            by sim-raise-ℂ _ one-ℂ))
```
