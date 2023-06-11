# Equality of natural numbers

```agda
module elementary-number-theory.equality-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.decidable-equality
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.set-truncations
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.decidable-propositions
```

</details>

## Properties

### The type of natural numbers has decidable equality

```agda
is-decidable-Eq-ℕ :
  (m n : ℕ) → is-decidable (Eq-ℕ m n)
is-decidable-Eq-ℕ zero-ℕ zero-ℕ = inl star
is-decidable-Eq-ℕ zero-ℕ (succ-ℕ n) = inr id
is-decidable-Eq-ℕ (succ-ℕ m) zero-ℕ = inr id
is-decidable-Eq-ℕ (succ-ℕ m) (succ-ℕ n) = is-decidable-Eq-ℕ m n

has-decidable-equality-ℕ : has-decidable-equality ℕ
has-decidable-equality-ℕ x y =
  is-decidable-iff (eq-Eq-ℕ x y) Eq-eq-ℕ (is-decidable-Eq-ℕ x y)

decidable-eq-ℕ : ℕ → ℕ → Decidable-Prop lzero
pr1 (decidable-eq-ℕ m n) = (m ＝ n)
pr1 (pr2 (decidable-eq-ℕ m n)) = is-set-ℕ m n
pr2 (pr2 (decidable-eq-ℕ m n)) = has-decidable-equality-ℕ m n

is-decidable-is-zero-ℕ : (n : ℕ) → is-decidable (is-zero-ℕ n)
is-decidable-is-zero-ℕ n = has-decidable-equality-ℕ n zero-ℕ

is-decidable-is-zero-ℕ' : (n : ℕ) → is-decidable (is-zero-ℕ' n)
is-decidable-is-zero-ℕ' n = has-decidable-equality-ℕ zero-ℕ n

is-decidable-is-nonzero-ℕ : (n : ℕ) → is-decidable (is-nonzero-ℕ n)
is-decidable-is-nonzero-ℕ n =
  is-decidable-neg (is-decidable-is-zero-ℕ n)

is-decidable-is-one-ℕ : (n : ℕ) → is-decidable (is-one-ℕ n)
is-decidable-is-one-ℕ n = has-decidable-equality-ℕ n 1

is-decidable-is-one-ℕ' : (n : ℕ) → is-decidable (is-one-ℕ' n)
is-decidable-is-one-ℕ' n = has-decidable-equality-ℕ 1 n

is-decidable-is-not-one-ℕ :
  (x : ℕ) → is-decidable (is-not-one-ℕ x)
is-decidable-is-not-one-ℕ x =
  is-decidable-neg (is-decidable-is-one-ℕ x)
```

## The full characterization of the identity type of ℕ

```agda
map-total-Eq-ℕ :
  (m : ℕ) → Σ ℕ (Eq-ℕ m) → Σ ℕ (Eq-ℕ (succ-ℕ m))
pr1 (map-total-Eq-ℕ m (pair n e)) = succ-ℕ n
pr2 (map-total-Eq-ℕ m (pair n e)) = e

is-contr-total-Eq-ℕ :
  (m : ℕ) → is-contr (Σ ℕ (Eq-ℕ m))
pr1 (pr1 (is-contr-total-Eq-ℕ m)) = m
pr2 (pr1 (is-contr-total-Eq-ℕ m)) = refl-Eq-ℕ m
pr2 (is-contr-total-Eq-ℕ zero-ℕ) (pair zero-ℕ star) = refl
pr2 (is-contr-total-Eq-ℕ (succ-ℕ m)) (pair (succ-ℕ n) e) =
  ap (map-total-Eq-ℕ m) (pr2 (is-contr-total-Eq-ℕ m) (pair n e))

is-equiv-Eq-eq-ℕ :
  {m n : ℕ} → is-equiv (Eq-eq-ℕ {m} {n})
is-equiv-Eq-eq-ℕ {m} {n} =
  fundamental-theorem-id
    ( is-contr-total-Eq-ℕ m)
    ( λ y → Eq-eq-ℕ {m} {y})
    ( n)
```

### The type of natural numbers is its own set truncation

```agda
equiv-unit-trunc-ℕ-Set : ℕ ≃ type-trunc-Set ℕ
equiv-unit-trunc-ℕ-Set = equiv-unit-trunc-Set ℕ-Set
```
