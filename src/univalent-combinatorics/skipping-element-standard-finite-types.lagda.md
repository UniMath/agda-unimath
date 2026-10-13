# Skipping elements in standard finite types

```agda
module univalent-combinatorics.skipping-element-standard-finite-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.empty-types
open import foundation.equality-coproduct-types
open import foundation.fibers-of-maps
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.negated-equality
open import foundation.sets
open import foundation.unit-type

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Given a [natural number](elementary-number-theory.natural-numbers.md) `k` and
any value `x : Fin (succ-ℕ k)`, we define an
[embedding](foundation-core.embeddings.md) `skip-Fin : Fin k → Fin (succ-ℕ k)`
whose image contains every value of `Fin (succ-ℕ k)` except `x`.

## Definition

```agda
skip-Fin :
  (k : ℕ) → Fin (succ-ℕ k) → Fin k → Fin (succ-ℕ k)
skip-Fin (succ-ℕ k) (inl x) (inl y) = inl (skip-Fin k x y)
skip-Fin (succ-ℕ k) (inl x) (inr y) = inr star
skip-Fin (succ-ℕ k) (inr x) y = inl y
```

## Properties

### `skip-Fin` is injective

```agda
abstract
  is-injective-skip-Fin :
    (k : ℕ) (x : Fin (succ-ℕ k)) → is-injective (skip-Fin k x)
  is-injective-skip-Fin (succ-ℕ k) (inl x) {inl y} {inl z} p =
    ap inl (is-injective-skip-Fin k x (is-injective-is-emb is-emb-inl p))
  is-injective-skip-Fin (succ-ℕ k) (inl x) {inr star} {inr star} p = refl
  is-injective-skip-Fin (succ-ℕ k) (inr star) =
    is-injective-is-emb is-emb-inl
```

### `skip-Fin` is an embedding

```agda
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

### `x` is not in the image of `skip-Fin k x`

```agda
abstract
  nonequal-skip-Fin :
    (k : ℕ) (x : Fin (succ-ℕ k)) (i : Fin k) → skip-Fin k x i ≠ x
  nonequal-skip-Fin (succ-ℕ k) (inl x) (inl i) skxi=x =
    nonequal-skip-Fin k x i (is-injective-inl skxi=x)
```

### Every element of `Fin (succ-ℕ k)` that is nonequal to `x` is in the image of `skip-Fin k x`

```agda
opaque
  fiber-skip-Fin :
    (k : ℕ) (x : Fin (succ-ℕ k)) (i : Fin (succ-ℕ k)) → x ≠ i →
    fiber (skip-Fin k x) i
  fiber-skip-Fin zero-ℕ (inr star) (inr star) x≠i = ex-falso (x≠i refl)
  fiber-skip-Fin (succ-ℕ k) (inl x) (inl i) x≠i =
    let (j , skxj=i) = fiber-skip-Fin k x i (nonequal-map inl x≠i)
    in (inl j , ap inl skxj=i)
  fiber-skip-Fin (succ-ℕ k) (inl x) (inr star) x≠i =
    ( inr star , refl)
  fiber-skip-Fin (succ-ℕ k) (inr star) (inl i) x≠i =
    ( i , refl)
  fiber-skip-Fin (succ-ℕ k) (inr star) (inr star) x≠i = ex-falso (x≠i refl)
```
