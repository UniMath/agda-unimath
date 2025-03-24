# Maximum on the standard finite types

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module elementary-number-theory.maximum-standard-finite-types
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

open import order-theory.least-upper-bounds-posets funext univalence truncations

open import univalent-combinatorics.standard-finite-types funext univalence truncations
```

</details>

## Idea

We define the operation of maximum (least upper bound) for the standard finite
types.

## Definition

```agda
max-Fin : (k : ℕ) → Fin k → Fin k → Fin k
max-Fin (succ-ℕ k) (inl x) (inl y) = inl (max-Fin k x y)
max-Fin (succ-ℕ k) (inl x) (inr _) = inr star
max-Fin (succ-ℕ k) (inr _) (inl x) = inr star
max-Fin (succ-ℕ k) (inr _) (inr _) = inr star

max-Fin-Fin : (n k : ℕ) → (Fin (succ-ℕ n) → Fin k) → Fin k
max-Fin-Fin zero-ℕ k f =
  f (inr star)
max-Fin-Fin (succ-ℕ n) k f =
  max-Fin k (f (inr star)) (max-Fin-Fin n k (λ k → f (inl k)))
```

## Properties

### Maximum is greatest lower bound

```agda
leq-max-Fin :
  (k : ℕ) (l m n : Fin k) →
  leq-Fin k m l → leq-Fin k n l → leq-Fin k (max-Fin k m n) l
leq-max-Fin (succ-ℕ k) (inl x) (inl y) (inl z) p q = leq-max-Fin k x y z p q
leq-max-Fin (succ-ℕ k) (inr x) (inl y) (inl z) p q = star
leq-max-Fin (succ-ℕ k) (inr x) (inl y) (inr z) p q = star
leq-max-Fin (succ-ℕ k) (inr x) (inr y) (inl z) p q = star
leq-max-Fin (succ-ℕ k) (inr x) (inr y) (inr z) p q = star

leq-left-leq-max-Fin :
  (k : ℕ) (l m n : Fin k) → leq-Fin k (max-Fin k m n) l → leq-Fin k m l
leq-left-leq-max-Fin (succ-ℕ k) (inl x) (inl y) (inl z) p =
  leq-left-leq-max-Fin k x y z p
leq-left-leq-max-Fin (succ-ℕ k) (inr x) (inl y) (inl z) p = star
leq-left-leq-max-Fin (succ-ℕ k) (inr x) (inl y) (inr z) p = star
leq-left-leq-max-Fin (succ-ℕ k) (inr x) (inr y) (inl z) p = star
leq-left-leq-max-Fin (succ-ℕ k) (inr x) (inr y) (inr z) p = star
leq-left-leq-max-Fin (succ-ℕ k) (inl x) (inr y) (inr z) p = p

leq-right-leq-max-Fin :
  (k : ℕ) (l m n : Fin k) → leq-Fin k (max-Fin k m n) l → leq-Fin k n l
leq-right-leq-max-Fin (succ-ℕ k) (inl x) (inl y) (inl z) p =
  leq-right-leq-max-Fin k x y z p
leq-right-leq-max-Fin (succ-ℕ k) (inr x) (inl y) (inl z) p = star
leq-right-leq-max-Fin (succ-ℕ k) (inr x) (inl y) (inr z) p = star
leq-right-leq-max-Fin (succ-ℕ k) (inr x) (inr y) (inl z) p = star
leq-right-leq-max-Fin (succ-ℕ k) (inr x) (inr y) (inr z) p = star
leq-right-leq-max-Fin (succ-ℕ k) (inl x) (inl y) (inr z) p = p

is-least-upper-bound-max-Fin :
  (k : ℕ) (m n : Fin k) →
  is-least-binary-upper-bound-Poset (Fin-Poset k) m n (max-Fin k m n)
is-least-upper-bound-max-Fin k m n =
  prove-is-least-binary-upper-bound-Poset
    ( Fin-Poset k)
    ( ( leq-left-leq-max-Fin k
        ( max-Fin k m n)
        ( m)
        ( n)
        ( refl-leq-Fin k (max-Fin k m n))) ,
      ( leq-right-leq-max-Fin k
        ( max-Fin k m n)
        ( m)
        ( n)
        ( refl-leq-Fin k (max-Fin k m n))))
    ( λ x (H , K) → leq-max-Fin k x m n H K)
```
