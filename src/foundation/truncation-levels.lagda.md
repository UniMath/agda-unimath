# Truncation levels

```agda
module foundation.truncation-levels where

open import foundation-core.truncation-levels public
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions

open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
```

</details>

## Definitions

### Inclusions of the natural numbers into the truncation levels

```agda
truncation-level-minus-two-ℕ : ℕ → 𝕋
truncation-level-minus-two-ℕ zero-ℕ = neg-two-𝕋
truncation-level-minus-two-ℕ (succ-ℕ n) =
  succ-𝕋 (truncation-level-minus-two-ℕ n)

truncation-level-minus-one-ℕ : ℕ → 𝕋
truncation-level-minus-one-ℕ = succ-𝕋 ∘ truncation-level-minus-two-ℕ

truncation-level-ℕ : ℕ → 𝕋
truncation-level-ℕ = succ-𝕋 ∘ truncation-level-minus-one-ℕ
```

### Inclusion of the double successors of truncation levels into the natural numbers

```agda
nat+2-𝕋 : 𝕋 → ℕ
nat+2-𝕋 neg-two-𝕋 = zero-ℕ
nat+2-𝕋 (succ-𝕋 k) = succ-ℕ (nat+2-𝕋 k)
```
