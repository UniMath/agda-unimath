# Equality in the standard finite types

```agda
module univalent-combinatorics.equality-standard-finite-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.apartness-relations
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.discrete-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.functoriality-coproduct-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.negated-equality
open import foundation.negation
open import foundation.propositions
open import foundation.set-truncations
open import foundation.tight-apartness-relations
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.decidable-propositions

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Since the standard finite types are defined recursively by adding a point one at
a time, it follows that equality in the standard finite types is decidable, and
that they are sets.

## Properties

### Characterization of the identity types of the standard finite types

```agda
Eq-Fin : (k : ℕ) → Fin k → Fin k → UU lzero
Eq-Fin (succ-ℕ k) (inl x) (inl y) = Eq-Fin k x y
Eq-Fin (succ-ℕ k) (inl x) (inr y) = empty
Eq-Fin (succ-ℕ k) (inr x) (inl y) = empty
Eq-Fin (succ-ℕ k) (inr x) (inr y) = unit

is-prop-Eq-Fin : (k : ℕ) → (x : Fin k) → (y : Fin k) → is-prop (Eq-Fin k x y)
is-prop-Eq-Fin (succ-ℕ k) (inl x) (inl y) = is-prop-Eq-Fin k x y
is-prop-Eq-Fin (succ-ℕ k) (inr x) (inl y) = is-prop-empty
is-prop-Eq-Fin (succ-ℕ k) (inl x) (inr y) = is-prop-empty
is-prop-Eq-Fin (succ-ℕ k) (inr x) (inr y) = is-prop-unit

refl-Eq-Fin : (k : ℕ) (x : Fin k) → Eq-Fin k x x
refl-Eq-Fin (succ-ℕ k) (inl x) = refl-Eq-Fin k x
refl-Eq-Fin (succ-ℕ k) (inr x) = star

Eq-Fin-eq : (k : ℕ) {x y : Fin k} → x ＝ y → Eq-Fin k x y
Eq-Fin-eq k refl = refl-Eq-Fin k _

eq-Eq-Fin :
  (k : ℕ) {x y : Fin k} → Eq-Fin k x y → x ＝ y
eq-Eq-Fin (succ-ℕ k) {inl x} {inl y} e = ap inl (eq-Eq-Fin k e)
eq-Eq-Fin (succ-ℕ k) {inr star} {inr star} star = refl

extensionality-Fin :
  (k : ℕ)
  (x y : Fin k) →
  (x ＝ y) ≃ (Eq-Fin k x y)
pr1 (extensionality-Fin k x y) = Eq-Fin-eq k
pr2 (extensionality-Fin k x y) =
  is-equiv-has-converse-is-prop
    ( is-set-Fin k x y)
    ( is-prop-Eq-Fin k x y)
    ( eq-Eq-Fin k)

is-decidable-Eq-Fin : (k : ℕ) (x y : Fin k) → is-decidable (Eq-Fin k x y)
is-decidable-Eq-Fin (succ-ℕ k) (inl x) (inl y) = is-decidable-Eq-Fin k x y
is-decidable-Eq-Fin (succ-ℕ k) (inl x) (inr y) = is-decidable-empty
is-decidable-Eq-Fin (succ-ℕ k) (inr x) (inl y) = is-decidable-empty
is-decidable-Eq-Fin (succ-ℕ k) (inr x) (inr y) = is-decidable-unit

has-decidable-equality-Fin :
  (k : ℕ) (x y : Fin k) → is-decidable (Id x y)
has-decidable-equality-Fin k x y =
  map-coproduct
    ( eq-Eq-Fin k)
    ( map-neg (Eq-Fin-eq k))
    ( is-decidable-Eq-Fin k x y)

Fin-Discrete-Type : ℕ → Discrete-Type lzero
pr1 (Fin-Discrete-Type k) = Fin k
pr2 (Fin-Discrete-Type k) = has-decidable-equality-Fin k

is-decidable-is-zero-Fin :
  {k : ℕ} (x : Fin k) → is-decidable (is-zero-Fin k x)
is-decidable-is-zero-Fin {succ-ℕ k} x =
  has-decidable-equality-Fin (succ-ℕ k) x (zero-Fin k)

is-decidable-is-neg-one-Fin :
  {k : ℕ} (x : Fin k) → is-decidable (is-neg-one-Fin k x)
is-decidable-is-neg-one-Fin {succ-ℕ k} x =
  has-decidable-equality-Fin (succ-ℕ k) x (neg-one-Fin k)

is-decidable-is-one-Fin :
  {k : ℕ} (x : Fin k) → is-decidable (is-one-Fin k x)
is-decidable-is-one-Fin {succ-ℕ k} x =
  has-decidable-equality-Fin (succ-ℕ k) x (one-Fin k)
```

### Being zero or being one is a proposition

```agda
is-prop-is-zero-Fin :
  (k : ℕ) (x : Fin (succ-ℕ k)) → is-prop (is-zero-Fin (succ-ℕ k) x)
is-prop-is-zero-Fin k x = is-set-Fin (succ-ℕ k) x (zero-Fin k)

is-prop-is-one-Fin :
  (k : ℕ) (x : Fin (succ-ℕ k)) → is-prop (is-one-Fin (succ-ℕ k) x)
is-prop-is-one-Fin k x = is-set-Fin (succ-ℕ k) x (one-Fin k)

is-prop-is-zero-or-one-Fin-2 :
  (x : Fin 2) → is-prop ((is-zero-Fin 2 x) + (is-one-Fin 2 x))
is-prop-is-zero-or-one-Fin-2 x =
  is-prop-coproduct
    ( λ p q → Eq-Fin-eq 2 (inv p ∙ q))
    ( is-prop-is-zero-Fin 1 x)
    ( is-prop-is-one-Fin 1 x)
```

### Every element in the standard two-element type is either `0` or `1`

```agda
is-contr-is-zero-or-one-Fin-2 :
  (x : Fin 2) → is-contr ((is-zero-Fin 2 x) + (is-one-Fin 2 x))
is-contr-is-zero-or-one-Fin-2 x =
  is-proof-irrelevant-is-prop
    ( is-prop-is-zero-or-one-Fin-2 x)
    ( is-zero-or-one-Fin-2 x)
```

```agda
decidable-Eq-Fin :
  (n : ℕ) (i j : Fin n) → Decidable-Prop lzero
pr1 (decidable-Eq-Fin n i j) = i ＝ j
pr1 (pr2 (decidable-Eq-Fin n i j)) = is-set-Fin n i j
pr2 (pr2 (decidable-Eq-Fin n i j)) = has-decidable-equality-Fin n i j
```

### The standard finite types are their own set truncations

```agda
equiv-unit-trunc-Fin-Set : (k : ℕ) → Fin k ≃ type-trunc-Set (Fin k)
equiv-unit-trunc-Fin-Set k = equiv-unit-trunc-Set (Fin-Set k)
```

### If `leq-ℕ 2 n`, then there exists two distinct elements in `Fin n`

```agda
two-distinct-elements-leq-2-Fin :
  (n : ℕ) → leq-ℕ 2 n → Σ (Fin n) (λ x → Σ (Fin n) (λ y → x ≠ y))
pr1 (two-distinct-elements-leq-2-Fin (succ-ℕ (succ-ℕ n)) ineq) =
  inr star
pr1 (pr2 (two-distinct-elements-leq-2-Fin (succ-ℕ (succ-ℕ n)) ineq)) =
  inl (inr star)
pr2 (pr2 (two-distinct-elements-leq-2-Fin (succ-ℕ (succ-ℕ n)) ineq)) =
  neq-inr-inl
```

### The standard finite type with a (tight) apartness relation

```agda
Fin-Type-With-Apartness : (k : ℕ) → Type-With-Apartness lzero lzero
Fin-Type-With-Apartness k =
  type-with-apartness-Discrete-Type (Fin-Discrete-Type k)

Fin-Type-With-Tight-Apartness : (k : ℕ) → Type-With-Tight-Apartness lzero lzero
Fin-Type-With-Tight-Apartness k =
  type-with-tight-apartness-Discrete-Type (Fin-Discrete-Type k)
```
