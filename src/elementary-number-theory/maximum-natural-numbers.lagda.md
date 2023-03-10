# Maximum on the natural numbers

```agda
module elementary-number-theory.maximum-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.unit-type

open import order-theory.least-upper-bounds-posets

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

We define the operation of maximum (least upper bound) for the natural numbers.

## Definition

```agda
max-ℕ : ℕ → (ℕ → ℕ)
max-ℕ 0 n = n
max-ℕ (succ-ℕ m) 0 = succ-ℕ m
max-ℕ (succ-ℕ m) (succ-ℕ n) = succ-ℕ (max-ℕ m n)

max-Fin-ℕ : (n : ℕ) → (Fin n → ℕ) → ℕ
max-Fin-ℕ zero-ℕ f = zero-ℕ
max-Fin-ℕ (succ-ℕ n) f = max-ℕ (f (inr star)) (max-Fin-ℕ n (λ k → f (inl k)))
```

## Properties

### Maximum is a least upper bound

```agda
leq-max-ℕ :
  (k m n : ℕ) → m ≤-ℕ k → n ≤-ℕ k → (max-ℕ m n) ≤-ℕ k
leq-max-ℕ zero-ℕ zero-ℕ zero-ℕ H K = star
leq-max-ℕ (succ-ℕ k) zero-ℕ zero-ℕ H K = star
leq-max-ℕ (succ-ℕ k) zero-ℕ (succ-ℕ n) H K = K
leq-max-ℕ (succ-ℕ k) (succ-ℕ m) zero-ℕ H K = H
leq-max-ℕ (succ-ℕ k) (succ-ℕ m) (succ-ℕ n) H K = leq-max-ℕ k m n H K

leq-left-leq-max-ℕ :
  (k m n : ℕ) → (max-ℕ m n) ≤-ℕ k → m ≤-ℕ k
leq-left-leq-max-ℕ k zero-ℕ zero-ℕ H = star
leq-left-leq-max-ℕ k zero-ℕ (succ-ℕ n) H = star
leq-left-leq-max-ℕ k (succ-ℕ m) zero-ℕ H = H
leq-left-leq-max-ℕ (succ-ℕ k) (succ-ℕ m) (succ-ℕ n) H =
  leq-left-leq-max-ℕ k m n H

leq-right-leq-max-ℕ :
  (k m n : ℕ) → (max-ℕ m n) ≤-ℕ k → n ≤-ℕ k
leq-right-leq-max-ℕ k zero-ℕ zero-ℕ H = star
leq-right-leq-max-ℕ k zero-ℕ (succ-ℕ n) H = H
leq-right-leq-max-ℕ k (succ-ℕ m) zero-ℕ H = star
leq-right-leq-max-ℕ (succ-ℕ k) (succ-ℕ m) (succ-ℕ n) H =
  leq-right-leq-max-ℕ k m n H

is-least-upper-bound-max-ℕ :
  (m n : ℕ) → is-least-binary-upper-bound-Poset ℕ-Poset m n (max-ℕ m n)
is-least-upper-bound-max-ℕ m n =
  ( leq-left-leq-max-ℕ (max-ℕ m n) m n (refl-leq-ℕ (max-ℕ m n)),
    leq-right-leq-max-ℕ (max-ℕ m n) m n (refl-leq-ℕ (max-ℕ m n))),
  λ x (m≤x , n≤x) → leq-max-ℕ x m n m≤x n≤x
```
