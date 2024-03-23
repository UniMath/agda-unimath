# The positive integers

```agda
module elementary-number-theory.positive-integers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.integers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.decidable-subtypes
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
open import foundation.transport-along-identifications
open import foundation.unit-type
open import foundation.universe-levels
```

</details>

## Idea

The positive integers are `one-ℤ` and its successors.

## Defintions

### Positive integers

```agda
is-positive-ℤ : ℤ → UU lzero
is-positive-ℤ (inl x) = empty
is-positive-ℤ (inr (inl x)) = empty
is-positive-ℤ (inr (inr x)) = unit

is-prop-is-positive-ℤ : (x : ℤ) → is-prop (is-positive-ℤ x)
is-prop-is-positive-ℤ (inl x) = is-prop-empty
is-prop-is-positive-ℤ (inr (inl x)) = is-prop-empty
is-prop-is-positive-ℤ (inr (inr x)) = is-prop-unit

subtype-positive-ℤ : subtype lzero ℤ
subtype-positive-ℤ x = (is-positive-ℤ x , is-prop-is-positive-ℤ x)

positive-ℤ : UU lzero
positive-ℤ = type-subtype subtype-positive-ℤ

is-positive-eq-ℤ : {x y : ℤ} → x ＝ y → is-positive-ℤ x → is-positive-ℤ y
is-positive-eq-ℤ = tr is-positive-ℤ

module _
  (p : positive-ℤ)
  where

  int-positive-ℤ : ℤ
  int-positive-ℤ = pr1 p

  is-positive-int-positive-ℤ : is-positive-ℤ int-positive-ℤ
  is-positive-int-positive-ℤ = pr2 p
```

### Positive constants

```agda
one-positive-ℤ : positive-ℤ
one-positive-ℤ = (one-ℤ , star)
```

## Properties

### Positivity is decidable

```agda
is-decidable-is-positive-ℤ : is-decidable-fam is-positive-ℤ
is-decidable-is-positive-ℤ (inl x) = inr id
is-decidable-is-positive-ℤ (inr (inl x)) = inr id
is-decidable-is-positive-ℤ (inr (inr x)) = inl star

decidable-subtype-positive-ℤ : decidable-subtype lzero ℤ
decidable-subtype-positive-ℤ x =
  ( is-positive-ℤ x ,
    is-prop-is-positive-ℤ x ,
    is-decidable-is-positive-ℤ x)
```

### The positive integers are a `Set`

```agda
is-set-positive-ℤ : is-set positive-ℤ
is-set-positive-ℤ =
  is-set-type-subtype subtype-positive-ℤ is-set-ℤ
```

### The successor of a positive integer is positive

```agda
is-positive-succ-is-positive-ℤ :
  {x : ℤ} → is-positive-ℤ x → is-positive-ℤ (succ-ℤ x)
is-positive-succ-is-positive-ℤ {inr (inr x)} H = H

succ-positive-ℤ : positive-ℤ → positive-ℤ
succ-positive-ℤ (x , H) = (succ-ℤ x , is-positive-succ-is-positive-ℤ H)
```

### The integer image of a nonzero natural number is positive

```agda
is-positive-int-is-nonzero-ℕ :
  (x : ℕ) → is-nonzero-ℕ x → is-positive-ℤ (int-ℕ x)
is-positive-int-is-nonzero-ℕ zero-ℕ H = ex-falso (H refl)
is-positive-int-is-nonzero-ℕ (succ-ℕ x) H = star
```

### The canonical equivalence between natural numbers and positive integers

```agda
positive-int-ℕ : ℕ → positive-ℤ
positive-int-ℕ = rec-ℕ one-positive-ℤ (λ _ → succ-positive-ℤ)

nat-positive-ℤ : positive-ℤ → ℕ
nat-positive-ℤ (inr (inr x) , H) = x

eq-nat-positive-succ-positive-ℤ :
  (x : positive-ℤ) →
  nat-positive-ℤ (succ-positive-ℤ x) ＝ succ-ℕ (nat-positive-ℤ x)
eq-nat-positive-succ-positive-ℤ (inr (inr x) , H) = refl

is-section-nat-positive-ℤ :
  (x : positive-ℤ) → positive-int-ℕ (nat-positive-ℤ x) ＝ x
is-section-nat-positive-ℤ (inr (inr zero-ℕ) , H) = refl
is-section-nat-positive-ℤ (inr (inr (succ-ℕ x)) , H) =
  ap succ-positive-ℤ (is-section-nat-positive-ℤ ( inr (inr x) , H))

is-retraction-nat-positive-ℤ :
  (n : ℕ) → nat-positive-ℤ (positive-int-ℕ n) ＝ n
is-retraction-nat-positive-ℤ zero-ℕ = refl
is-retraction-nat-positive-ℤ (succ-ℕ n) =
  eq-nat-positive-succ-positive-ℤ (positive-int-ℕ n) ∙
  ap succ-ℕ (is-retraction-nat-positive-ℤ n)

is-equiv-positive-int-ℕ : is-equiv positive-int-ℕ
pr1 (pr1 is-equiv-positive-int-ℕ) = nat-positive-ℤ
pr2 (pr1 is-equiv-positive-int-ℕ) = is-section-nat-positive-ℤ
pr1 (pr2 is-equiv-positive-int-ℕ) = nat-positive-ℤ
pr2 (pr2 is-equiv-positive-int-ℕ) = is-retraction-nat-positive-ℤ

equiv-positive-int-ℕ : ℕ ≃ positive-ℤ
pr1 equiv-positive-int-ℕ = positive-int-ℕ
pr2 equiv-positive-int-ℕ = is-equiv-positive-int-ℕ
```

## See also

- The relations between positive and nonnegative, negative and nonnpositive
  integers are derived in
  [`positive-and-negative-integers`](elementary-number-theory.positive-and-negative-integers.md)
