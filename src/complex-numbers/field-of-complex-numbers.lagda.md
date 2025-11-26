# The field of complex numbers

```agda
module complex-numbers.field-of-complex-numbers where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.heyting-fields
open import commutative-algebra.homomorphisms-heyting-fields
open import commutative-algebra.invertible-elements-commutative-rings

open import complex-numbers.apartness-complex-numbers
open import complex-numbers.complex-numbers
open import complex-numbers.large-ring-of-complex-numbers
open import complex-numbers.local-ring-of-complex-numbers
open import complex-numbers.multiplicative-inverses-nonzero-complex-numbers
open import complex-numbers.raising-universe-levels-complex-numbers

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.negation
open import foundation.universe-levels

open import real-numbers.field-of-real-numbers
```

</details>

## Idea

The [complex numbers](complex-numbers.complex-numbers.md) form a
[Heyting field](commutative-algebra.heyting-fields.md).

## Definition

```agda
abstract
  is-zero-is-noninvertible-commutative-ring-ℂ :
    (l : Level) (z : ℂ l) →
    ¬ (is-invertible-element-Commutative-Ring (commutative-ring-ℂ l) z) →
    z ＝ raise-ℂ l zero-ℂ
  is-zero-is-noninvertible-commutative-ring-ℂ l z ¬inv-z =
    is-tight-apartness-relation-ℂ l z (raise-ℂ l zero-ℂ)
      ( λ z#0 →
        ¬inv-z
          ( is-invertible-is-nonzero-ℂ
            ( z)
            ( apart-right-sim-ℂ
              ( z)
              ( raise-ℂ l zero-ℂ)
              ( zero-ℂ)
              ( sim-raise-ℂ' l zero-ℂ)
              ( z#0))))

is-heyting-field-local-commutative-ring-ℂ :
  (l : Level) →
  is-heyting-field-Local-Commutative-Ring (local-commutative-ring-ℂ l)
is-heyting-field-local-commutative-ring-ℂ l =
  ( neq-raise-zero-one-ℂ l ,
    is-zero-is-noninvertible-commutative-ring-ℂ l)

heyting-field-ℂ : (l : Level) → Heyting-Field (lsuc l)
heyting-field-ℂ l =
  ( local-commutative-ring-ℂ l ,
    is-heyting-field-local-commutative-ring-ℂ l)
```

## Properties

### The canonical field homomorphism from the real numbers to the complex numbers

```agda
hom-heyting-field-ℝ-ℂ :
  (l : Level) → hom-Heyting-Field (heyting-field-ℝ l) (heyting-field-ℂ l)
hom-heyting-field-ℝ-ℂ l = hom-ring-ℝ-ℂ l
```
