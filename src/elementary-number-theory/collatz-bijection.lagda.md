# The Collatz bijection

```agda
module elementary-number-theory.collatz-bijection where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.distance-natural-numbers
open import elementary-number-theory.euclidean-division-natural-numbers
open import elementary-number-theory.modular-arithmetic
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.coproduct-types
open import foundation.identity-types
```

</details>

## Idea

We define a bijection of Collatz

## Definition

```agda
cases-map-collatz-bijection : (n : ℕ) (x : ℤ-Mod 3) (p : mod-ℕ 3 n ＝ x) → ℕ
cases-map-collatz-bijection n (inl (inl (inr star))) p =
  quotient-euclidean-division-ℕ 3 (2 *ℕ n)
cases-map-collatz-bijection n (inl (inr star)) p =
  quotient-euclidean-division-ℕ 3 (dist-ℕ (4 *ℕ n) 1)
cases-map-collatz-bijection n (inr star) p =
  quotient-euclidean-division-ℕ 3 (succ-ℕ (4 *ℕ n))

map-collatz-bijection : ℕ → ℕ
map-collatz-bijection n = cases-map-collatz-bijection n (mod-ℕ 3 n) refl
```
