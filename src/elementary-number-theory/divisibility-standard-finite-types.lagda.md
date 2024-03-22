# The divisibility relation on the standard finite types

```agda
module elementary-number-theory.divisibility-standard-finite-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.modular-arithmetic-standard-finite-types
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import univalent-combinatorics.decidable-dependent-pair-types
open import univalent-combinatorics.equality-standard-finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Given two elements `x y : Fin k`, we say that `x` divides `y` if there is an
element `u : Fin k` such that `mul-Fin u x = y`.

## Definition

```agda
div-Fin : (k : ℕ) → Fin k → Fin k → UU lzero
div-Fin k x y = Σ (Fin k) (λ u → mul-Fin k u x ＝ y)
```

## Properties

### The divisibility relation is reflexive

```agda
refl-div-Fin : {k : ℕ} (x : Fin k) → div-Fin k x x
pr1 (refl-div-Fin {succ-ℕ k} x) = one-Fin k
pr2 (refl-div-Fin {succ-ℕ k} x) = left-unit-law-mul-Fin k x
```

### The divisibility relation is transitive

```agda
transitive-div-Fin :
  (k : ℕ) → is-transitive (div-Fin k)
pr1 (transitive-div-Fin k x y z (pair v q) (pair u p)) = mul-Fin k v u
pr2 (transitive-div-Fin k x y z (pair v q) (pair u p)) =
  associative-mul-Fin k v u x ∙ (ap (mul-Fin k v) p ∙ q)
```

### Every element divides zero

```agda
div-zero-Fin : (k : ℕ) (x : Fin (succ-ℕ k)) → div-Fin (succ-ℕ k) x (zero-Fin k)
pr1 (div-zero-Fin k x) = zero-Fin k
pr2 (div-zero-Fin k x) = left-zero-law-mul-Fin k x
```

### Every element is divisible by one

```agda
div-one-Fin : (k : ℕ) (x : Fin (succ-ℕ k)) → div-Fin (succ-ℕ k) (one-Fin k) x
pr1 (div-one-Fin k x) = x
pr2 (div-one-Fin k x) = right-unit-law-mul-Fin k x
```

### The only element that is divisible by zero is zero itself

```agda
is-zero-div-zero-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) →
  div-Fin (succ-ℕ k) (zero-Fin k) x → is-zero-Fin (succ-ℕ k) x
is-zero-div-zero-Fin {k} x (pair u p) = inv p ∙ right-zero-law-mul-Fin k u
```

### The divisibility relation is decidable

```agda
is-decidable-div-Fin : (k : ℕ) (x y : Fin k) → is-decidable (div-Fin k x y)
is-decidable-div-Fin k x y =
  is-decidable-Σ-Fin k (λ u → has-decidable-equality-Fin k (mul-Fin k u x) y)
```
