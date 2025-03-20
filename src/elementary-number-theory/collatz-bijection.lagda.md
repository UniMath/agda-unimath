# The Collatz bijection

```agda
open import foundation.function-extensionality-axiom

module
  elementary-number-theory.collatz-bijection
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.distance-natural-numbers funext
open import elementary-number-theory.euclidean-division-natural-numbers funext
open import elementary-number-theory.modular-arithmetic funext
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.coproduct-types funext
open import foundation.identity-types funext
```

</details>

## Idea

We define a bijection of Collatz

## Definition

```agda
cases-map-collatz-bijection : (n : ℕ) (x : ℤ-Mod 3) (p : mod-ℕ 3 n ＝ x) → ℕ
cases-map-collatz-bijection n (inl (inl (inr _))) p =
  quotient-euclidean-division-ℕ 3 (2 *ℕ n)
cases-map-collatz-bijection n (inl (inr _)) p =
  quotient-euclidean-division-ℕ 3 (dist-ℕ (4 *ℕ n) 1)
cases-map-collatz-bijection n (inr _) p =
  quotient-euclidean-division-ℕ 3 (succ-ℕ (4 *ℕ n))

map-collatz-bijection : ℕ → ℕ
map-collatz-bijection n = cases-map-collatz-bijection n (mod-ℕ 3 n) refl
```
