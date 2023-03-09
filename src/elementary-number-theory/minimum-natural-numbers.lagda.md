# Minimum on the natural numbers

```agda
module elementary-number-theory.minimum-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.unit-type

open import order-theory.greatest-lower-bounds-posets

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

We define the operation of minimum (greatest lower bound) for the natural numbers.

## Definition

```agda
min-ℕ : ℕ → (ℕ → ℕ)
min-ℕ 0 n = 0
min-ℕ (succ-ℕ m) 0 = 0
min-ℕ (succ-ℕ m) (succ-ℕ n) = succ-ℕ (min-ℕ m n)

min-Fin-ℕ : (n : ℕ) → (Fin (succ-ℕ n) → ℕ) → ℕ
min-Fin-ℕ zero-ℕ f = f (inr star)
min-Fin-ℕ (succ-ℕ n) f = min-ℕ (f (inr star)) (min-Fin-ℕ n (λ k → f (inl k)))
```

## Properties

### Minimum is a greatest lower bound

```agda
leq-min-ℕ :
  (k m n : ℕ) → k ≤-ℕ m → k ≤-ℕ n → k ≤-ℕ (min-ℕ m n)
leq-min-ℕ zero-ℕ zero-ℕ zero-ℕ H K = star
leq-min-ℕ zero-ℕ zero-ℕ (succ-ℕ n) H K = star
leq-min-ℕ zero-ℕ (succ-ℕ m) zero-ℕ H K = star
leq-min-ℕ zero-ℕ (succ-ℕ m) (succ-ℕ n) H K = star
leq-min-ℕ (succ-ℕ k) (succ-ℕ m) (succ-ℕ n) H K = leq-min-ℕ k m n H K

leq-left-leq-min-ℕ :
  (k m n : ℕ) → k ≤-ℕ (min-ℕ m n) → k ≤-ℕ m
leq-left-leq-min-ℕ zero-ℕ zero-ℕ zero-ℕ H = star
leq-left-leq-min-ℕ zero-ℕ zero-ℕ (succ-ℕ n) H = star
leq-left-leq-min-ℕ zero-ℕ (succ-ℕ m) zero-ℕ H = star
leq-left-leq-min-ℕ zero-ℕ (succ-ℕ m) (succ-ℕ n) H = star
leq-left-leq-min-ℕ (succ-ℕ k) (succ-ℕ m) (succ-ℕ n) H =
  leq-left-leq-min-ℕ k m n H

leq-right-leq-min-ℕ :
  (k m n : ℕ) → k ≤-ℕ (min-ℕ m n) → k ≤-ℕ n
leq-right-leq-min-ℕ zero-ℕ zero-ℕ zero-ℕ H = star
leq-right-leq-min-ℕ zero-ℕ zero-ℕ (succ-ℕ n) H = star
leq-right-leq-min-ℕ zero-ℕ (succ-ℕ m) zero-ℕ H = star
leq-right-leq-min-ℕ zero-ℕ (succ-ℕ m) (succ-ℕ n) H = star
leq-right-leq-min-ℕ (succ-ℕ k) (succ-ℕ m) (succ-ℕ n) H =
  leq-right-leq-min-ℕ k m n H

is-greatest-lower-bound-min-ℕ :
  (l m : ℕ) → is-greatest-binary-lower-bound-Poset ℕ-Poset l m (min-ℕ l m)
is-greatest-lower-bound-min-ℕ l m =
  ( leq-left-leq-min-ℕ (min-ℕ l m) l m (refl-leq-ℕ (min-ℕ l m)),
    leq-right-leq-min-ℕ (min-ℕ l m) l m (refl-leq-ℕ (min-ℕ l m))),
  λ x (x≤l , x≤m) → leq-min-ℕ x l m x≤l x≤m
```
