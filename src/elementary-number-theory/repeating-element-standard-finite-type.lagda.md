# Repeating an element in a standard finite type

```agda
module elementary-number-theory.repeating-element-standard-finite-type where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.empty-types
open import foundation.identity-types
open import foundation.negation

open import univalent-combinatorics.equality-standard-finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

```agda
repeat-Fin :
  (k : ℕ) (x : Fin k) → Fin (succ-ℕ k) → Fin k
repeat-Fin (succ-ℕ k) (inl x) (inl y) = inl (repeat-Fin k x y)
repeat-Fin (succ-ℕ k) (inl x) (inr star) = inr star
repeat-Fin (succ-ℕ k) (inr star) (inl y) = y
repeat-Fin (succ-ℕ k) (inr star) (inr star) = inr star

abstract
  is-almost-injective-repeat-Fin :
    (k : ℕ) (x : Fin k) {y z : Fin (succ-ℕ k)} →
    ¬ (inl x ＝ y) → ¬ (inl x ＝ z) →
    repeat-Fin k x y ＝ repeat-Fin k x z → y ＝ z
  is-almost-injective-repeat-Fin (succ-ℕ k) (inl x) {inl y} {inl z} f g p =
    ap
      ( inl)
      ( is-almost-injective-repeat-Fin k x
        ( λ q → f (ap inl q))
        ( λ q → g (ap inl q))
        ( is-injective-inl p))
  is-almost-injective-repeat-Fin (succ-ℕ k) (inl x) {inl y} {inr star} f g p =
    ex-falso (Eq-Fin-eq (succ-ℕ k) p)
  is-almost-injective-repeat-Fin (succ-ℕ k) (inl x) {inr star} {inl z} f g p =
    ex-falso (Eq-Fin-eq (succ-ℕ k) p)
  is-almost-injective-repeat-Fin
    (succ-ℕ k) (inl x) {inr star} {inr star} f g p =
    refl
  is-almost-injective-repeat-Fin (succ-ℕ k) (inr star) {inl y} {inl z} f g p =
    ap inl p
  is-almost-injective-repeat-Fin
    (succ-ℕ k) (inr star) {inl y} {inr star} f g p =
    ex-falso (f (ap inl (inv p)))
  is-almost-injective-repeat-Fin
    (succ-ℕ k) (inr star) {inr star} {inl z} f g p =
    ex-falso (g (ap inl p))
  is-almost-injective-repeat-Fin
    (succ-ℕ k) (inr star) {inr star} {inr star} f g p = refl
```
