# The Archimedean property of the integers

```agda
module elementary-number-theory.archimedean-property-integers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.archimedean-property-natural-numbers
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonnegative-integers
open import elementary-number-theory.positive-and-negative-integers
open import elementary-number-theory.positive-integers
open import elementary-number-theory.strict-inequality-integers

open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.unit-type
```

</details>

## Definition

The
{{#concept "Archimedean property" Disambiguation="integers" Agda=archimedean-property-ℤ}}
of the [integers](elementary-number-theory.integers.md) is that for any
[positive integer](elementary-number-theory.positive-integers.md) `x` and
integer `y`, there is an `n : ℕ` such that `y < int-ℕ n *ℤ x`.

```agda
abstract
  archimedean-property-ℤ :
    (x y : ℤ) → is-positive-ℤ x → exists ℕ (λ n → le-ℤ-Prop y (int-ℕ n *ℤ x))
  archimedean-property-ℤ x y pos-x with decide-is-negative-is-nonnegative-ℤ {y}
  ... | inl neg-y = intro-exists zero-ℕ (le-zero-is-negative-ℤ y neg-y)
  ... | inr nonneg-y =
      ind-Σ
        ( λ nx (nonzero-nx , nx=x) →
          elim-exists
            (∃ ℕ (λ n → le-ℤ-Prop y (int-ℕ n *ℤ x)))
            ( λ n ny<n*nx →
              intro-exists
                ( n)
                ( binary-tr
                  ( le-ℤ)
                  ( ap pr1 (is-section-nat-nonnegative-ℤ (y , nonneg-y)))
                  ( inv (mul-int-ℕ n nx) ∙ ap (int-ℕ n *ℤ_) nx=x)
                  ( le-natural-le-ℤ
                    ( nat-nonnegative-ℤ (y , nonneg-y))
                    ( n *ℕ nx)
                    ( ny<n*nx))))
            ( archimedean-property-ℕ
              ( nx)
              ( nat-nonnegative-ℤ (y , nonneg-y)) nonzero-nx))
        (pos-ℤ-to-ℕ x pos-x)
    where pos-ℤ-to-ℕ :
            (z : ℤ) →
              is-positive-ℤ z →
              Σ ℕ (λ n → is-nonzero-ℕ n × (int-ℕ n ＝ z))
          pos-ℤ-to-ℕ (inr (inr n)) H = succ-ℕ n , (λ ()) , refl
```

## External links

- [Archimedean property](https://en.wikipedia.org/wiki/Archimedean_property) at
  Wikipedia
