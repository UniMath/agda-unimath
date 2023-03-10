# Skipping elements in standard finite types

```agda
module univalent-combinatorics.skipping-element-standard-finite-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equality-coproduct-types
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.unit-type

open import univalent-combinatorics.standard-finite-types
```

</details>

```agda
skip-Fin :
  (k : ℕ) → Fin (succ-ℕ k) → Fin k → Fin (succ-ℕ k)
skip-Fin (succ-ℕ k) (inl x) (inl y) = inl (skip-Fin k x y)
skip-Fin (succ-ℕ k) (inl x) (inr y) = inr star
skip-Fin (succ-ℕ k) (inr x) y = inl y

abstract
  is-injective-skip-Fin :
    (k : ℕ) (x : Fin (succ-ℕ k)) → is-injective (skip-Fin k x)
  is-injective-skip-Fin (succ-ℕ k) (inl x) {inl y} {inl z} p =
    ap ( inl)
       ( is-injective-skip-Fin k x
         ( is-injective-is-emb (is-emb-inl (Fin (succ-ℕ k)) unit) p))
  is-injective-skip-Fin (succ-ℕ k) (inl x) {inr star} {inr star} p = refl
  is-injective-skip-Fin (succ-ℕ k) (inr star) {y} {z} p =
    is-injective-is-emb (is-emb-inl (Fin (succ-ℕ k)) unit) p

abstract
  is-emb-skip-Fin :
    (k : ℕ) (x : Fin (succ-ℕ k)) → is-emb (skip-Fin k x)
  is-emb-skip-Fin k x =
    is-emb-is-injective
      ( is-set-Fin (succ-ℕ k))
      ( is-injective-skip-Fin k x)

emb-skip-Fin : (k : ℕ) (x : Fin (succ-ℕ k)) → Fin k ↪ Fin (succ-ℕ k)
pr1 (emb-skip-Fin k x) = skip-Fin k x
pr2 (emb-skip-Fin k x) = is-emb-skip-Fin k x
```
