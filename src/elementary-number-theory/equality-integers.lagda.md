# Equality of integers

```agda
module elementary-number-theory.equality-integers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.integers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.decidable-equality
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.discrete-types
open import foundation.empty-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.set-truncations
open import foundation.torsorial-type-families
open import foundation.unit-type
open import foundation.universe-levels
```

</details>

## Idea

We define equality on the [integers](elementary-number-theory.integers.md) by
pattern matching, and show that this characterizes the
[identity type](foundation.identity-types.md) on the integers.

## Definition

```agda
Eq-ℤ : ℤ → ℤ → UU lzero
Eq-ℤ (inl x) (inl y) = Eq-ℕ x y
Eq-ℤ (inl x) (inr y) = empty
Eq-ℤ (inr x) (inl y) = empty
Eq-ℤ (inr (inl x)) (inr (inl y)) = unit
Eq-ℤ (inr (inl x)) (inr (inr y)) = empty
Eq-ℤ (inr (inr x)) (inr (inl y)) = empty
Eq-ℤ (inr (inr x)) (inr (inr y)) = Eq-ℕ x y

refl-Eq-ℤ : (x : ℤ) → Eq-ℤ x x
refl-Eq-ℤ (inl x) = refl-Eq-ℕ x
refl-Eq-ℤ (inr (inl x)) = star
refl-Eq-ℤ (inr (inr x)) = refl-Eq-ℕ x

Eq-eq-ℤ : {x y : ℤ} → x ＝ y → Eq-ℤ x y
Eq-eq-ℤ {x} {.x} refl = refl-Eq-ℤ x

eq-Eq-ℤ : (x y : ℤ) → Eq-ℤ x y → x ＝ y
eq-Eq-ℤ (inl x) (inl y) e = ap inl (eq-Eq-ℕ x y e)
eq-Eq-ℤ (inr (inl star)) (inr (inl star)) e = refl
eq-Eq-ℤ (inr (inr x)) (inr (inr y)) e = ap (inr ∘ inr) (eq-Eq-ℕ x y e)
```

## Properties

### Equality on the integers is decidable

```agda
has-decidable-equality-ℤ : has-decidable-equality ℤ
has-decidable-equality-ℤ =
  has-decidable-equality-coproduct
    has-decidable-equality-ℕ
    ( has-decidable-equality-coproduct
      has-decidable-equality-unit
      has-decidable-equality-ℕ)

is-decidable-is-zero-ℤ :
  (x : ℤ) → is-decidable (is-zero-ℤ x)
is-decidable-is-zero-ℤ x = has-decidable-equality-ℤ x zero-ℤ

is-decidable-is-one-ℤ :
  (x : ℤ) → is-decidable (is-one-ℤ x)
is-decidable-is-one-ℤ x = has-decidable-equality-ℤ x one-ℤ

is-decidable-is-neg-one-ℤ :
  (x : ℤ) → is-decidable (is-neg-one-ℤ x)
is-decidable-is-neg-one-ℤ x = has-decidable-equality-ℤ x neg-one-ℤ

ℤ-Discrete-Type : Discrete-Type lzero
pr1 ℤ-Discrete-Type = ℤ
pr2 ℤ-Discrete-Type = has-decidable-equality-ℤ
```

### The type of integers is its own set truncation

```agda
equiv-unit-trunc-ℤ-Set : ℤ ≃ type-trunc-Set ℤ
equiv-unit-trunc-ℤ-Set = equiv-unit-trunc-Set ℤ-Set
```

### Equality on the integers is a proposition

```agda
is-prop-Eq-ℤ :
  (x y : ℤ) → is-prop (Eq-ℤ x y)
is-prop-Eq-ℤ (inl x) (inl y) = is-prop-Eq-ℕ x y
is-prop-Eq-ℤ (inl x) (inr y) = is-prop-empty
is-prop-Eq-ℤ (inr x) (inl x₁) = is-prop-empty
is-prop-Eq-ℤ (inr (inl x)) (inr (inl y)) = is-prop-unit
is-prop-Eq-ℤ (inr (inl x)) (inr (inr y)) = is-prop-empty
is-prop-Eq-ℤ (inr (inr x)) (inr (inl y)) = is-prop-empty
is-prop-Eq-ℤ (inr (inr x)) (inr (inr y)) = is-prop-Eq-ℕ x y

Eq-ℤ-eq :
  {x y : ℤ} → x ＝ y → Eq-ℤ x y
Eq-ℤ-eq {x} {.x} refl = refl-Eq-ℤ x

contraction-total-Eq-ℤ :
  (x : ℤ) (y : Σ ℤ (Eq-ℤ x)) → pair x (refl-Eq-ℤ x) ＝ y
contraction-total-Eq-ℤ (inl x) (pair (inl y) e) =
  eq-pair-Σ
    ( ap inl (eq-Eq-ℕ x y e))
    ( eq-is-prop (is-prop-Eq-ℕ x y))
contraction-total-Eq-ℤ (inr (inl star)) (pair (inr (inl star)) e) =
  eq-pair-eq-fiber (eq-is-prop is-prop-unit)
contraction-total-Eq-ℤ (inr (inr x)) (pair (inr (inr y)) e) =
  eq-pair-Σ
    ( ap (inr ∘ inr) (eq-Eq-ℕ x y e))
    ( eq-is-prop (is-prop-Eq-ℕ x y))

is-torsorial-Eq-ℤ :
  (x : ℤ) → is-torsorial (Eq-ℤ x)
is-torsorial-Eq-ℤ x =
  pair (pair x (refl-Eq-ℤ x)) (contraction-total-Eq-ℤ x)

is-equiv-Eq-ℤ-eq :
  (x y : ℤ) → is-equiv (Eq-ℤ-eq {x} {y})
is-equiv-Eq-ℤ-eq x =
  fundamental-theorem-id
    ( is-torsorial-Eq-ℤ x)
    ( λ y → Eq-ℤ-eq {x} {y})
```
