# Skipping elements in standard finite types

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module univalent-combinatorics.skipping-element-standard-finite-types
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types funext univalence truncations
open import foundation.dependent-pair-types
open import foundation.embeddings funext
open import foundation.equality-coproduct-types funext univalence truncations
open import foundation.identity-types funext
open import foundation.injective-maps funext
open import foundation.sets funext univalence
open import foundation.unit-type

open import univalent-combinatorics.standard-finite-types funext univalence truncations
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
    ap inl (is-injective-skip-Fin k x (is-injective-is-emb is-emb-inl p))
  is-injective-skip-Fin (succ-ℕ k) (inl x) {inr star} {inr star} p = refl
  is-injective-skip-Fin (succ-ℕ k) (inr star) =
    is-injective-is-emb is-emb-inl

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
