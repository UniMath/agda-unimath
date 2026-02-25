# Addition of nonzero complex numbers

```agda
module complex-numbers.addition-nonzero-complex-numbers where
```

<details><summary>Imports</summary>

```agda
open import complex-numbers.addition-complex-numbers
open import complex-numbers.complex-numbers
open import complex-numbers.nonzero-complex-numbers

open import foundation.disjunction
open import foundation.functoriality-disjunction
open import foundation.universe-levels

open import real-numbers.addition-nonzero-real-numbers
open import real-numbers.nonzero-real-numbers
```

</details>

## Idea

This file describes properties of
[addition](complex-numbers.addition-complex-numbers.md) of
[nonzero](complex-numbers.nonzero-complex-numbers.md)
[complex numbers](complex-numbers.complex-numbers.md).

## Properties

### If the sum of two complex numbers is nonzero, one of them is nonzero

```agda
abstract
  is-nonzero-either-is-nonzero-add-ℂ :
    {l1 l2 : Level} (z : ℂ l1) (w : ℂ l2) → is-nonzero-ℂ (z +ℂ w) →
    disjunction-type (is-nonzero-ℂ z) (is-nonzero-ℂ w)
  is-nonzero-either-is-nonzero-add-ℂ z@(a +iℂ b) w@(c +iℂ d) =
    elim-disjunction
      ( is-nonzero-prop-ℂ z ∨ is-nonzero-prop-ℂ w)
      ( λ a+c≠0 →
        map-disjunction
          ( inl-disjunction)
          ( inl-disjunction)
          ( is-nonzero-either-is-nonzero-add-ℝ a c a+c≠0))
      ( λ b+d≠0 →
        map-disjunction
          ( inr-disjunction)
          ( inr-disjunction)
          ( is-nonzero-either-is-nonzero-add-ℝ b d b+d≠0))
```
