# The Archimedean property of the integers

```agda
module elementary-number-theory.archimedean-integers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.archimedean-natural-numbers
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.positive-and-negative-integers
open import elementary-number-theory.positive-integers
open import elementary-number-theory.strict-inequality-integers

open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.unit-type
```

</details>

## Definition

The Archimedean property of the integers is that for any positive integer `x` and integer `y`,
there is an `n : ℕ` such that `y < int-ℕ n *ℤ x`.

```agda
archimedean-property-ℤ : (x y : ℤ) → is-positive-ℤ x → Σ ℕ (λ n → le-ℤ y (int-ℕ n *ℤ x))
archimedean-property-ℤ x y pos-x with decide-sign-ℤ {y}
... | inl neg-y = zero-ℕ , le-zero-is-negative-ℤ y neg-y
... | inr (inl refl) = 1 , le-zero-is-positive-ℤ x pos-x
... | inr (inr pos-y) =
    ind-Σ
      (λ nx (nonzero-nx , nx=x) →
        ind-Σ
          (λ ny (_ , ny=y) →
            ind-Σ
              (λ n y<n*nx →
                n ,
                  binary-tr
                    le-ℤ
                    ny=y
                    (inv (mul-int-ℕ n nx) ∙ ap (int-ℕ n *ℤ_) nx=x)
                    (le-natural-le-ℤ ny (n *ℕ nx) y<n*nx))
              (archimedean-property-ℕ nx ny nonzero-nx))
          (pos-ℤ-to-ℕ y pos-y))
      (pos-ℤ-to-ℕ x pos-x)
  where pos-ℤ-to-ℕ :
          (z : ℤ) →
            is-positive-ℤ z →
            Σ ℕ (λ n → is-nonzero-ℕ n × (int-ℕ n ＝ z))
        pos-ℤ-to-ℕ (inr (inr n)) H = succ-ℕ n , (λ ()) , refl
```

## External links

- [Archimedean property](https://en.wikipedia.org/wiki/Archimedean_property)
  at Wikipedia
