# Truncation levels

```agda
module foundation.truncation-levels where
```

<details><summary>Imports</summary>

```agda
open import foundation-core.truncation-levels public

open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation-core.functions
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

### Addition of truncation levels

```agda
add-𝕋 : 𝕋 → 𝕋 → 𝕋
add-𝕋 neg-two-𝕋 neg-two-𝕋 = neg-two-𝕋
add-𝕋 neg-two-𝕋 (succ-𝕋 neg-two-𝕋) = neg-two-𝕋
add-𝕋 neg-two-𝕋 (succ-𝕋 (succ-𝕋 l)) = l
add-𝕋 (succ-𝕋 neg-two-𝕋) neg-two-𝕋 = neg-two-𝕋
add-𝕋 (succ-𝕋 neg-two-𝕋) (succ-𝕋 l) = l
add-𝕋 (succ-𝕋 (succ-𝕋 k)) neg-two-𝕋 = k
add-𝕋 (succ-𝕋 (succ-𝕋 k)) (succ-𝕋 l) = succ-𝕋 (add-𝕋 (succ-𝕋 k) (succ-𝕋 l))
```

## Properties

### Unit laws for addition of truncation levels

```agda
left-unit-law-add-𝕋 : (k : 𝕋) → add-𝕋 zero-𝕋 k ＝ k
left-unit-law-add-𝕋 neg-two-𝕋 = refl
left-unit-law-add-𝕋 (succ-𝕋 neg-two-𝕋) = refl
left-unit-law-add-𝕋 (succ-𝕋 (succ-𝕋 neg-two-𝕋)) = refl
left-unit-law-add-𝕋 (succ-𝕋 (succ-𝕋 (succ-𝕋 k))) = refl

right-unit-law-add-𝕋 : (k : 𝕋) → add-𝕋 k zero-𝕋 ＝ k
right-unit-law-add-𝕋 neg-two-𝕋 = refl
right-unit-law-add-𝕋 (succ-𝕋 neg-two-𝕋) = refl
right-unit-law-add-𝕋 (succ-𝕋 (succ-𝕋 k)) =
  ap succ-𝕋 (right-unit-law-add-𝕋 (succ-𝕋 k))
```

### Successor laws for addition of truncation levels

```agda
left-successor-law-add-𝕋 :
  (n k : 𝕋) →
  add-𝕋 (succ-𝕋 (succ-𝕋 (succ-𝕋 n))) k ＝
  succ-𝕋 (add-𝕋 (succ-𝕋 (succ-𝕋 n)) k)
left-successor-law-add-𝕋 n neg-two-𝕋 = refl
left-successor-law-add-𝕋 n (succ-𝕋 k) = refl

right-successor-law-add-𝕋 :
  (k n : 𝕋) →
  add-𝕋 k (succ-𝕋 (succ-𝕋 (succ-𝕋 n))) ＝
  succ-𝕋 (add-𝕋 k (succ-𝕋 (succ-𝕋 n)))
right-successor-law-add-𝕋 neg-two-𝕋 n = refl
right-successor-law-add-𝕋 (succ-𝕋 neg-two-𝕋) n = refl
right-successor-law-add-𝕋 (succ-𝕋 (succ-𝕋 k)) n =
  ap succ-𝕋 (right-successor-law-add-𝕋 (succ-𝕋 k) n)
```
