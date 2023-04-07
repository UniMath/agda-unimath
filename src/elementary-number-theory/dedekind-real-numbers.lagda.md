# Dedekind real numbers

```agda
module elementary-number-theory.dedekind-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.rational-numbers

open import foundation.dependent-pair-types
open import foundation.logical-equivalences
open import foundation.coproduct-types
open import foundation.cartesian-product-types
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.negation
open import foundation.propositions
open import foundation.universe-levels
```

</details>

## Idea

A dedekind real number `x` is a pair of maps `(L , U)` from `ℚ` to `Prop`,
with `L` representing all the rationals smaller than `x`, and
`U` representing all the rationals greater than `x`.

## Definition

```agda
is-dedekind-cut :
  (ℚ → Prop lzero) × (ℚ → Prop lzero) → UU lzero
is-dedekind-cut (L , U) =
  (((exists ℚ L × exists ℚ U) ×
  ((q r : ℚ) →
    (L q ⇔ ∃-Prop ℚ (λ r → le-ℚ q r × type-Prop (L r))) ×
    (U q ⇔ ∃-Prop ℚ (λ q → le-ℚ q r × type-Prop (U q))))) ×
  ((q : ℚ) → ¬ (type-Prop (L q) × type-Prop (U q)))) ×
  ((q r : ℚ) → le-ℚ q r → type-Prop (L q) + type-Prop (U q))

dedekind-ℝ : UU (lsuc lzero)
dedekind-ℝ = Σ ((ℚ → Prop lzero) × (ℚ → Prop lzero)) is-dedekind-cut
```
