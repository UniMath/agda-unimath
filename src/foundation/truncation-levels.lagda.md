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

### Inclusion of the truncation levels into the natural numbers

```agda
nat-succ-succ-𝕋 : 𝕋 → ℕ
nat-succ-succ-𝕋 neg-two-𝕋 = zero-ℕ
nat-succ-succ-𝕋 (succ-𝕋 k) = succ-ℕ (nat-succ-succ-𝕋 k)
```

### The iterated successor on truncation levels

Although we can define an addition operation on truncation levels, when it comes
to doing induction on them, it is more natural to speak in terms of an iterated
successor:

```agda
iterated-succ-𝕋 : ℕ → 𝕋 → 𝕋
iterated-succ-𝕋 zero-ℕ x = x
iterated-succ-𝕋 (succ-ℕ n) x = iterated-succ-𝕋 n (succ-𝕋 x)

iterated-succ-𝕋' : 𝕋 → ℕ → 𝕋
iterated-succ-𝕋' x n = iterated-succ-𝕋 n x

iterated-succ-𝕋'' : ℕ → 𝕋 → 𝕋
iterated-succ-𝕋'' zero-ℕ x = x
iterated-succ-𝕋'' (succ-ℕ n) x = succ-𝕋 (iterated-succ-𝕋 n x)
```

### The two definitions of the iterated successor agree

```agda
reassociate-iterated-succ-𝕋 :
  (n : ℕ) (k : 𝕋) → iterated-succ-𝕋 (succ-ℕ n) k ＝ succ-𝕋 (iterated-succ-𝕋 n k)
reassociate-iterated-succ-𝕋 zero-ℕ k = refl
reassociate-iterated-succ-𝕋 (succ-ℕ n) k =
  reassociate-iterated-succ-𝕋 n (succ-𝕋 k)

compute-iterated-succ-𝕋 : (n : ℕ) → iterated-succ-𝕋 n ~ iterated-succ-𝕋'' n
compute-iterated-succ-𝕋 zero-ℕ = refl-htpy
compute-iterated-succ-𝕋 (succ-ℕ n) k = reassociate-iterated-succ-𝕋 n k
```
