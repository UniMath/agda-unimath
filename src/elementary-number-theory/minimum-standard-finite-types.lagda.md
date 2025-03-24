# Minimum on the standard finite types

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module elementary-number-theory.minimum-standard-finite-types
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-standard-finite-types funext univalence truncations
open import elementary-number-theory.natural-numbers

open import foundation.coproduct-types funext univalence truncations
open import foundation.dependent-pair-types
open import foundation.unit-type

open import order-theory.greatest-lower-bounds-posets funext univalence truncations

open import univalent-combinatorics.standard-finite-types funext univalence truncations
```

</details>

## Idea

We define the operation of minimum (greatest lower bound) for the standard
finite types.

## Definition

```agda
min-Fin : (k : ℕ) → Fin k → Fin k → Fin k
min-Fin (succ-ℕ k) (inl x) (inl y) = inl (min-Fin k x y)
min-Fin (succ-ℕ k) (inl x) (inr _) = inl x
min-Fin (succ-ℕ k) (inr _) (inl x) = inl x
min-Fin (succ-ℕ k) (inr _) (inr _) = inr star

min-Fin-Fin : (n k : ℕ) → (Fin (succ-ℕ n) → Fin k) → Fin k
min-Fin-Fin zero-ℕ k f = f (inr star)
min-Fin-Fin (succ-ℕ n) k f =
  min-Fin k (f (inr star)) (min-Fin-Fin n k (λ k → f (inl k)))
```

## Properties

### Minimum is a greatest lower bound

We prove that `min-Fin` is a greatest lower bound of its two arguments by
showing that `min(m,n) ≤ x` is equivalent to `(m ≤ x) ∧ (n ≤ x)`, in components.
By reflexivity of `≤`, we compute that `min(m,n) ≤ m` (and correspondingly for
`n`).

```agda
leq-min-Fin :
  (k : ℕ) (l m n : Fin k) →
  leq-Fin k l m → leq-Fin k l n → leq-Fin k l (min-Fin k m n)
leq-min-Fin (succ-ℕ k) (inl x) (inl y) (inl z) p q = leq-min-Fin k x y z p q
leq-min-Fin (succ-ℕ k) (inl x) (inl y) (inr z) p q = p
leq-min-Fin (succ-ℕ k) (inl x) (inr y) (inl z) p q = q
leq-min-Fin (succ-ℕ k) (inl x) (inr y) (inr z) p q = star
leq-min-Fin (succ-ℕ k) (inr x) (inr y) (inr z) p q = star

leq-left-leq-min-Fin :
  (k : ℕ) (l m n : Fin k) → leq-Fin k l (min-Fin k m n) → leq-Fin k l m
leq-left-leq-min-Fin (succ-ℕ k) (inl x) (inl y) (inl z) p =
  leq-left-leq-min-Fin k x y z p
leq-left-leq-min-Fin (succ-ℕ k) (inl x) (inl y) (inr _) p = p
leq-left-leq-min-Fin (succ-ℕ k) (inl x) (inr _) (inl _) p = star
leq-left-leq-min-Fin (succ-ℕ k) (inl x) (inr _) (inr _) p = star
leq-left-leq-min-Fin (succ-ℕ k) (inr _) (inl y) (inr _) p = p
leq-left-leq-min-Fin (succ-ℕ k) (inr _) (inr _) (inl _) p = star
leq-left-leq-min-Fin (succ-ℕ k) (inr _) (inr _) (inr _) p = star

leq-right-leq-min-Fin :
  (k : ℕ) (l m n : Fin k) → leq-Fin k l (min-Fin k m n) → leq-Fin k l n
leq-right-leq-min-Fin (succ-ℕ k) (inl x) (inl x₁) (inl x₂) p =
  leq-right-leq-min-Fin k x x₁ x₂ p
leq-right-leq-min-Fin (succ-ℕ k) (inl x) (inl x₁) (inr x₂) p = star
leq-right-leq-min-Fin (succ-ℕ k) (inl x) (inr x₁) (inl x₂) p = p
leq-right-leq-min-Fin (succ-ℕ k) (inl x) (inr x₁) (inr x₂) p = star
leq-right-leq-min-Fin (succ-ℕ k) (inr x) (inr x₁) (inr x₂) p = star
leq-right-leq-min-Fin (succ-ℕ k) (inr x) (inl x₁) (inl x₂) p = p
leq-right-leq-min-Fin (succ-ℕ k) (inr x) (inr x₁) (inl x₂) p = p

is-greatest-lower-bound-min-Fin :
  (k : ℕ) (l m : Fin k) →
  is-greatest-binary-lower-bound-Poset (Fin-Poset k) l m (min-Fin k l m)
is-greatest-lower-bound-min-Fin k l m =
  prove-is-greatest-binary-lower-bound-Poset
    ( Fin-Poset k)
    ( ( leq-left-leq-min-Fin k
        ( min-Fin k l m)
        ( l)
        ( m)
        ( refl-leq-Fin k (min-Fin k l m))) ,
      ( leq-right-leq-min-Fin k
        ( min-Fin k l m)
        ( l)
        ( m)
        ( refl-leq-Fin k (min-Fin k l m))))
    ( λ x (H , K) → leq-min-Fin k x l m H K)
```
