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

### Inclusion of the truncation levels into the natural numbers

```agda
nat-succ-succ-𝕋 : 𝕋 → ℕ
nat-succ-succ-𝕋 neg-two-𝕋 = zero-ℕ
nat-succ-succ-𝕋 (succ-𝕋 k) = succ-ℕ (nat-succ-succ-𝕋 k)
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

infixl 35 _+𝕋_
_+𝕋_ = add-𝕋
```

```agda
succ-succ-add-𝕋 : 𝕋 → 𝕋 → 𝕋
succ-succ-add-𝕋 x neg-two-𝕋 = x
succ-succ-add-𝕋 x (succ-𝕋 y) = succ-𝕋 (succ-succ-add-𝕋 x y)
```

### Iterated successor functions on truncation levels

Although we can define an addition operation on truncation levels, when it comes
to doing induction on them, it is more natural to speak in terms of an iterated
successor:

```agda
iterated-succ-𝕋 : ℕ → 𝕋 → 𝕋
iterated-succ-𝕋 zero-ℕ x = x
iterated-succ-𝕋 (succ-ℕ n) x = iterated-succ-𝕋 n (succ-𝕋 x)

iterated-succ-𝕋' : 𝕋 → ℕ → 𝕋
iterated-succ-𝕋' x n = iterated-succ-𝕋 n x
```

## Properties

### Unit laws for addition of truncation levels

```agda
left-unit-law-add-𝕋 : (k : 𝕋) → zero-𝕋 +𝕋 k ＝ k
left-unit-law-add-𝕋 neg-two-𝕋 = refl
left-unit-law-add-𝕋 (succ-𝕋 neg-two-𝕋) = refl
left-unit-law-add-𝕋 (succ-𝕋 (succ-𝕋 neg-two-𝕋)) = refl
left-unit-law-add-𝕋 (succ-𝕋 (succ-𝕋 (succ-𝕋 k))) = refl

right-unit-law-add-𝕋 : (k : 𝕋) → k +𝕋 zero-𝕋 ＝ k
right-unit-law-add-𝕋 neg-two-𝕋 = refl
right-unit-law-add-𝕋 (succ-𝕋 neg-two-𝕋) = refl
right-unit-law-add-𝕋 (succ-𝕋 (succ-𝕋 k)) =
  ap succ-𝕋 (right-unit-law-add-𝕋 (succ-𝕋 k))
```

### Successor laws for addition of truncation levels

```agda
left-successor-law-add-𝕋 :
  (n k : 𝕋) →
  (succ-𝕋 (succ-𝕋 (succ-𝕋 n))) +𝕋 k ＝
  succ-𝕋 (add-𝕋 (succ-𝕋 (succ-𝕋 n)) k)
left-successor-law-add-𝕋 n neg-two-𝕋 = refl
left-successor-law-add-𝕋 n (succ-𝕋 k) = refl

right-successor-law-add-𝕋 :
  (k n : 𝕋) →
  k +𝕋 (succ-𝕋 (succ-𝕋 (succ-𝕋 n))) ＝
  succ-𝕋 (k +𝕋 (succ-𝕋 (succ-𝕋 n)))
right-successor-law-add-𝕋 neg-two-𝕋 n = refl
right-successor-law-add-𝕋 (succ-𝕋 neg-two-𝕋) n = refl
right-successor-law-add-𝕋 (succ-𝕋 (succ-𝕋 k)) n =
  ap succ-𝕋 (right-successor-law-add-𝕋 (succ-𝕋 k) n)
```
