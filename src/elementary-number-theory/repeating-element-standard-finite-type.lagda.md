# Repeating an element in a standard finite type

```agda
open import foundation.function-extensionality-axiom

module
  elementary-number-theory.repeating-element-standard-finite-type
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types funext
open import foundation.empty-types funext
open import foundation.identity-types funext
open import foundation.negated-equality funext
open import foundation.unit-type

open import univalent-combinatorics.equality-standard-finite-types funext
open import univalent-combinatorics.standard-finite-types funext
```

</details>

```agda
repeat-Fin :
  (k : ℕ) (x : Fin k) → Fin (succ-ℕ k) → Fin k
repeat-Fin (succ-ℕ k) (inl x) (inl y) = inl (repeat-Fin k x y)
repeat-Fin (succ-ℕ k) (inl x) (inr _) = inr star
repeat-Fin (succ-ℕ k) (inr _) (inl y) = y
repeat-Fin (succ-ℕ k) (inr _) (inr _) = inr star

abstract
  is-almost-injective-repeat-Fin :
    (k : ℕ) (x : Fin k) {y z : Fin (succ-ℕ k)} →
    inl x ≠ y → inl x ≠ z →
    repeat-Fin k x y ＝ repeat-Fin k x z → y ＝ z
  is-almost-injective-repeat-Fin (succ-ℕ k) (inl x) {inl y} {inl z} f g p =
    ap
      ( inl)
      ( is-almost-injective-repeat-Fin k x
        ( λ q → f (ap inl q))
        ( λ q → g (ap inl q))
        ( is-injective-inl p))
  is-almost-injective-repeat-Fin (succ-ℕ k) (inl x) {inl y} {inr _} f g p =
    ex-falso (Eq-Fin-eq (succ-ℕ k) p)
  is-almost-injective-repeat-Fin (succ-ℕ k) (inl x) {inr _} {inl z} f g p =
    ex-falso (Eq-Fin-eq (succ-ℕ k) p)
  is-almost-injective-repeat-Fin
    (succ-ℕ k) (inl x) {inr _} {inr _} f g p =
    refl
  is-almost-injective-repeat-Fin (succ-ℕ k) (inr _) {inl y} {inl z} f g p =
    ap inl p
  is-almost-injective-repeat-Fin
    (succ-ℕ k) (inr _) {inl y} {inr _} f g p =
    ex-falso (f (ap inl (inv p)))
  is-almost-injective-repeat-Fin
    (succ-ℕ k) (inr _) {inr _} {inl z} f g p =
    ex-falso (g (ap inl p))
  is-almost-injective-repeat-Fin
    (succ-ℕ k) (inr _) {inr _} {inr _} f g p = refl
```
