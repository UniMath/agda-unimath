# The based induction principle of the natural numbers

```agda
module elementary-number-theory.based-induction-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.function-types
open import foundation.identity-types
open import foundation.universe-levels
```

</details>

## Idea

The **based induction principle** for the natural numbers asserts that for any
family `P` of types over `ℕ` and any natural number `k : ℕ`, equipped with

1. An element `p0 : P k`
2. A function `pS : (x : ℕ) → k ≤-ℕ x → P x → P (x + 1)` there is a function

```text
  based-ind-ℕ k P p0 pS : (x : ℕ) → k ≤-ℕ x → P x
```

such that

1. `based-ind-ℕ k P p0 pS k K ＝ p0` for any `K : k ≤-ℕ k`, and
2. `based-ind-ℕ k P p0 pS (n + 1) N' ＝ pS n N (based-ind-ℕ k P p0 pS n N` for
   any `N : k ≤-ℕ n` and any `N' : k ≤-ℕ n + 1`.

## Theorem

### The based induction principle for the natural numbers

```agda
based-ind-ℕ :
  {l : Level} (k : ℕ) (P : ℕ → UU l) →
  P k → ((n : ℕ) → k ≤-ℕ n → P n → P (succ-ℕ n)) → (n : ℕ) → k ≤-ℕ n → P n
based-ind-ℕ zero-ℕ P p0 pS zero-ℕ H = p0
based-ind-ℕ zero-ℕ P p0 pS (succ-ℕ n) H =
  pS n H (based-ind-ℕ 0 P p0 pS n (leq-zero-ℕ n))
based-ind-ℕ (succ-ℕ k) P p0 pS (succ-ℕ n) =
  based-ind-ℕ k (P ∘ succ-ℕ) p0 (pS ∘ succ-ℕ) n

compute-base-based-ind-ℕ :
  {l : Level} (k : ℕ) (P : ℕ → UU l) (p0 : P k) →
  (pS : (n : ℕ) → k ≤-ℕ n → P n → P (succ-ℕ n)) → (H : k ≤-ℕ k) →
  based-ind-ℕ k P p0 pS k H ＝ p0
compute-base-based-ind-ℕ zero-ℕ P p0 pS _ = refl
compute-base-based-ind-ℕ (succ-ℕ k) P p0 pS =
  compute-base-based-ind-ℕ k (P ∘ succ-ℕ) p0 (pS ∘ succ-ℕ)

compute-succ-based-ind-ℕ :
  {l : Level} (k : ℕ) (P : ℕ → UU l) (p0 : P k) →
  (pS : (n : ℕ) → k ≤-ℕ n → P n → P (succ-ℕ n)) →
  (n : ℕ) (N : k ≤-ℕ n) (N' : k ≤-ℕ succ-ℕ n) →
  based-ind-ℕ k P p0 pS (succ-ℕ n) N' ＝
  pS n N (based-ind-ℕ k P p0 pS n N)
compute-succ-based-ind-ℕ zero-ℕ P p0 pS zero-ℕ _ _ = refl
compute-succ-based-ind-ℕ zero-ℕ P p0 pS (succ-ℕ n) _ _ = refl
compute-succ-based-ind-ℕ (succ-ℕ k) P p0 pS (succ-ℕ n) =
  compute-succ-based-ind-ℕ k (P ∘ succ-ℕ) p0 (pS ∘ succ-ℕ) n
```

## See also

- The based strong induction principle is defined in
  [`based-strong-induction-natural-numbers`](elementary-number-theory.based-strong-induction-natural-numbers.md).
