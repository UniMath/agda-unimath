# The negative integers

```agda
module elementary-number-theory.negative-integers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.integers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.retractions
open import foundation.sections
open import foundation.sets
open import foundation.subtypes
open import foundation.unit-type
open import foundation.universe-levels
```

</details>

## Idea

The negative integers are `neg-one-ℤ` and its predecessors.

## Defintions

### Negative integers

```agda
is-negative-ℤ : ℤ → UU lzero
is-negative-ℤ (inl k) = unit
is-negative-ℤ (inr k) = empty

is-prop-is-negative-ℤ : (x : ℤ) → is-prop (is-negative-ℤ x)
is-prop-is-negative-ℤ (inl x) = is-prop-unit
is-prop-is-negative-ℤ (inr x) = is-prop-empty

subtype-negative-ℤ : subtype lzero ℤ
subtype-negative-ℤ x = is-negative-ℤ x , is-prop-is-negative-ℤ x

negative-ℤ : UU lzero
negative-ℤ = type-subtype subtype-negative-ℤ

is-negative-eq-ℤ : {x y : ℤ} → x ＝ y → is-negative-ℤ x → is-negative-ℤ y
is-negative-eq-ℤ {x} refl = id

module _
  (p : negative-ℤ)
  where

  int-negative-ℤ : ℤ
  int-negative-ℤ = pr1 p

  is-negative-int-negative-ℤ : is-negative-ℤ int-negative-ℤ
  is-negative-int-negative-ℤ = pr2 p
```

### Negative constants

```agda
neg-one-negative-ℤ : negative-ℤ
neg-one-negative-ℤ = neg-one-ℤ , star
```

## Properties

### Negativity is decidable

```agda
is-decidable-is-negative-ℤ : is-decidable-fam is-negative-ℤ
is-decidable-is-negative-ℤ (inl x) = inl star
is-decidable-is-negative-ℤ (inr x) = inr id
```

### The negative integers are a `Set`

```agda
is-set-negative-ℤ : is-set negative-ℤ
is-set-negative-ℤ =
  is-set-type-subtype (subtype-negative-ℤ) (is-set-ℤ)
```

### The predecessor of a negative integer is negative

```agda
is-negative-pred-is-negative-ℤ :
  {x : ℤ} → is-negative-ℤ x → is-negative-ℤ (pred-ℤ x)
is-negative-pred-is-negative-ℤ {inl x} H = H

pred-negative-ℤ : negative-ℤ → negative-ℤ
pred-negative-ℤ (x , H) = pred-ℤ x , is-negative-pred-is-negative-ℤ H
```

### The canonical equivalence between natural numbers and negative integers

```agda
negative-int-ℕ : ℕ → negative-ℤ
negative-int-ℕ = rec-ℕ neg-one-negative-ℤ (λ _ → pred-negative-ℤ)

nat-negative-ℤ : negative-ℤ → ℕ
nat-negative-ℤ (inl x , H) = x

eq-nat-negative-pred-negative-ℤ :
  (x : negative-ℤ) →
  nat-negative-ℤ (pred-negative-ℤ x) ＝ succ-ℕ (nat-negative-ℤ x)
eq-nat-negative-pred-negative-ℤ (inl x , H) = refl

is-section-nat-negative-ℤ :
  (x : negative-ℤ) → negative-int-ℕ (nat-negative-ℤ x) ＝ x
is-section-nat-negative-ℤ (inl zero-ℕ , H) = refl
is-section-nat-negative-ℤ (inl (succ-ℕ x) , H) =
  ap pred-negative-ℤ (is-section-nat-negative-ℤ (inl x , H))

is-retraction-nat-negative-ℤ :
  (n : ℕ) → nat-negative-ℤ (negative-int-ℕ n) ＝ n
is-retraction-nat-negative-ℤ zero-ℕ = refl
is-retraction-nat-negative-ℤ (succ-ℕ n) =
  eq-nat-negative-pred-negative-ℤ (negative-int-ℕ n) ∙
  ap succ-ℕ (is-retraction-nat-negative-ℤ n)

is-equiv-negative-int-ℕ : is-equiv negative-int-ℕ
pr1 (pr1 is-equiv-negative-int-ℕ) = nat-negative-ℤ
pr2 (pr1 is-equiv-negative-int-ℕ) = is-section-nat-negative-ℤ
pr1 (pr2 is-equiv-negative-int-ℕ) = nat-negative-ℤ
pr2 (pr2 is-equiv-negative-int-ℕ) = is-retraction-nat-negative-ℤ

equiv-negative-int-ℕ : ℕ ≃ negative-ℤ
pr1 equiv-negative-int-ℕ = negative-int-ℕ
pr2 equiv-negative-int-ℕ = is-equiv-negative-int-ℕ
```