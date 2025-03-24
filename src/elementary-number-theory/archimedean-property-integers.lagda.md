# The Archimedean property of the integers

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module elementary-number-theory.archimedean-property-integers
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.archimedean-property-natural-numbers funext univalence truncations
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integers funext univalence truncations
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonnegative-integers funext univalence truncations
open import elementary-number-theory.positive-and-negative-integers funext univalence truncations
open import elementary-number-theory.positive-integers funext univalence truncations
open import elementary-number-theory.strict-inequality-integers funext univalence truncations

open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.cartesian-product-types funext univalence
open import foundation.coproduct-types funext univalence truncations
open import foundation.dependent-pair-types
open import foundation.existential-quantification funext univalence truncations
open import foundation.identity-types funext
open import foundation.propositional-truncations funext univalence
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
  bound-archimedean-property-ℤ :
    (x y : ℤ) → is-positive-ℤ x → Σ ℕ (λ n → le-ℤ y (int-ℕ n *ℤ x))
  bound-archimedean-property-ℤ x y pos-x
    with decide-is-negative-is-nonnegative-ℤ {y}
  ... | inl neg-y = zero-ℕ , le-zero-is-negative-ℤ y neg-y
  ... | inr nonneg-y =
      let
        (nx , nonzero-nx , nx=x) = pos-ℤ-to-ℕ x pos-x
        (n , ny<n*nx) =
          bound-archimedean-property-ℕ
            ( nx)
            ( nat-nonnegative-ℤ (y , nonneg-y))
            ( nonzero-nx)
      in
        n ,
        binary-tr
          ( le-ℤ)
          ( ap pr1 (is-section-nat-nonnegative-ℤ (y , nonneg-y)))
          ( inv (mul-int-ℕ n nx) ∙ ap (int-ℕ n *ℤ_) nx=x)
          ( le-natural-le-ℤ
            ( nat-nonnegative-ℤ (y , nonneg-y))
            ( n *ℕ nx)
            ( ny<n*nx))
    where
      pos-ℤ-to-ℕ :
        (z : ℤ) →
        is-positive-ℤ z →
        Σ ℕ (λ n → is-nonzero-ℕ n × (int-ℕ n ＝ z))
      pos-ℤ-to-ℕ (inr (inr n)) H = succ-ℕ n , (λ ()) , refl

  archimedean-property-ℤ :
    (x y : ℤ) → is-positive-ℤ x → exists ℕ (λ n → le-ℤ-Prop y (int-ℕ n *ℤ x))
  archimedean-property-ℤ x y pos-x =
    unit-trunc-Prop (bound-archimedean-property-ℤ x y pos-x)
```

## External links

- [Archimedean property](https://en.wikipedia.org/wiki/Archimedean_property) at
  Wikipedia
