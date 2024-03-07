# The positive, negative, nonnegative and nonpositive integers

```agda
module elementary-number-theory.positive-and-negative-integers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.integers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.negative-integers
open import elementary-number-theory.nonnegative-integers
open import elementary-number-theory.nonpositive-integers
open import elementary-number-theory.positive-integers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.empty-types
open import foundation.equality-coproduct-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.negated-equality
open import foundation.negation
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

In this file, we outline basic relations between negative, nonpositive,
nonnegative, and positive integers.

## Properties

### The only nonnegative and nonpositive integer is `zero-ℤ`

```agda
is-zero-is-nonnegative-is-nonpositive-ℤ :
  {x : ℤ} → is-nonnegative-ℤ x → is-nonpositive-ℤ x → is-zero-ℤ x
is-zero-is-nonnegative-is-nonpositive-ℤ {inr (inl x)} H K = refl
```

### Dichotomy properties

#### A nonzero integer is either negative or positive

```agda
decide-sign-nonzero-ℤ :
  (x : ℤ) → x ≠ zero-ℤ → is-negative-ℤ x + is-positive-ℤ x
decide-sign-nonzero-ℤ (inl x) H = inl star
decide-sign-nonzero-ℤ (inr (inl x)) H = ex-falso (H refl)
decide-sign-nonzero-ℤ (inr (inr x)) H = inr star
```

#### An integer is either positive or nonpositive

```agda
decide-is-positive-is-nonpositive-ℤ :
  (x : ℤ) → is-positive-ℤ x + is-nonpositive-ℤ x
decide-is-positive-is-nonpositive-ℤ (inl x) = inr star
decide-is-positive-is-nonpositive-ℤ (inr (inl x)) = inr star
decide-is-positive-is-nonpositive-ℤ (inr (inr x)) = inl star
```

#### An integer is either negative or nonnegative

```agda
decide-is-negative-is-nonnegative-ℤ :
  (x : ℤ) → is-negative-ℤ x + is-nonnegative-ℤ x
decide-is-negative-is-nonnegative-ℤ (inl x) = inl star
decide-is-negative-is-nonnegative-ℤ (inr x) = inr star
```

#### An integer or its negative is nonnegative

```agda
decide-is-nonnegative-is-nonnegative-neg-ℤ :
  {x : ℤ} → (is-nonnegative-ℤ x) + (is-nonnegative-ℤ (neg-ℤ x))
decide-is-nonnegative-is-nonnegative-neg-ℤ {inl x} = inr star
decide-is-nonnegative-is-nonnegative-neg-ℤ {inr x} = inl star
```

#### An integer or its negative is nonpositive

```agda
decide-is-nonpositive-is-nonpositive-neg-ℤ :
  {x : ℤ} → (is-nonpositive-ℤ x) + (is-nonpositive-ℤ (neg-ℤ x))
decide-is-nonpositive-is-nonpositive-neg-ℤ {inl x} = inl star
decide-is-nonpositive-is-nonpositive-neg-ℤ {inr (inl x)} = inl star
decide-is-nonpositive-is-nonpositive-neg-ℤ {inr (inr x)} = inr star
```

### Inclusion properties

#### Positive integers are nonnegative

```agda
is-nonnegative-is-positive-ℤ : (x : ℤ) → is-positive-ℤ x → is-nonnegative-ℤ x
is-nonnegative-is-positive-ℤ (inr (inr x)) H = H
```

#### Negative integers are nonpositive

```agda
is-nonpositive-is-negative-ℤ : (x : ℤ) → is-negative-ℤ x → is-nonpositive-ℤ x
is-nonpositive-is-negative-ℤ (inl x) H = H
```

### Relations with `succ-ℤ`

#### The successor of a nonnegative integer is positive

```agda
is-positive-succ-is-nonnegative-ℤ :
  (x : ℤ) → is-nonnegative-ℤ x → is-positive-ℤ (succ-ℤ x)
is-positive-succ-is-nonnegative-ℤ (inr (inl x)) H = H
is-positive-succ-is-nonnegative-ℤ (inr (inr x)) H = H
```

#### The successor of a negative integer is nonpositive

```agda
is-nonpositive-succ-is-negative-ℤ :
  (x : ℤ) → is-negative-ℤ x → is-nonpositive-ℤ (succ-ℤ x)
is-nonpositive-succ-is-negative-ℤ (inl zero-ℕ) H = H
is-nonpositive-succ-is-negative-ℤ (inl (succ-ℕ x)) H = H
```

### Relations with `pred-ℤ`

#### The predecessor of a positive integer is nonnegative

```agda
is-nonnegative-pred-is-positive-ℤ :
  (x : ℤ) → is-positive-ℤ x → is-nonnegative-ℤ (pred-ℤ x)
is-nonnegative-pred-is-positive-ℤ (inr (inr zero-ℕ)) H = H
is-nonnegative-pred-is-positive-ℤ (inr (inr (succ-ℕ x))) H = H
```

#### The predecessor of a nonnpositive integer is negative

```agda
is-negative-pred-is-nonpositive-ℤ :
  (x : ℤ) → is-nonpositive-ℤ x → is-negative-ℤ (pred-ℤ x)
is-negative-pred-is-nonpositive-ℤ (inl x) H = H
is-negative-pred-is-nonpositive-ℤ (inr (inl x)) H = H
```

### Relations with `neg-ℤ`

#### The negative of a nonnegative integer is nonpositive

```agda
is-nonpositive-neg-is-nonnegative-ℤ :
  (x : ℤ) → is-nonnegative-ℤ x → is-nonpositive-ℤ (neg-ℤ x)
is-nonpositive-neg-is-nonnegative-ℤ (inr (inl x)) H = H
is-nonpositive-neg-is-nonnegative-ℤ (inr (inr x)) H = H
```

#### The negative of a nonpositive integer is nonnegative

```agda
is-nonnegative-neg-is-nonnpositive-ℤ :
  (x : ℤ) → is-nonpositive-ℤ x → is-nonnegative-ℤ (neg-ℤ x)
is-nonnegative-neg-is-nonnpositive-ℤ (inl x) H = H
is-nonnegative-neg-is-nonnpositive-ℤ (inr (inl x)) H = H
```

#### The negative of a positive integer is negative

```agda
is-negative-neg-is-positive-ℤ :
  (x : ℤ) → is-positive-ℤ x → is-negative-ℤ (neg-ℤ x)
is-negative-neg-is-positive-ℤ (inr (inr x)) H = H
```

#### The negative of a negative integer is positive

```agda
is-positive-neg-is-negative-ℤ :
  (x : ℤ) → is-negative-ℤ x → is-positive-ℤ (neg-ℤ x)
is-positive-neg-is-negative-ℤ (inl x) H = H
```

### Negated properties

#### Nonpositivity is negated positivity

```agda
not-is-positive-is-nonpositive-ℤ :
  (x : ℤ) → is-nonpositive-ℤ x → ¬ (is-positive-ℤ x)
not-is-positive-is-nonpositive-ℤ (inr (inl x)) _ q = q
not-is-positive-is-nonpositive-ℤ (inr (inr x)) p _ = p

is-nonpositive-not-is-positive-ℤ :
  (x : ℤ) → ¬ (is-positive-ℤ x) → is-nonpositive-ℤ x
is-nonpositive-not-is-positive-ℤ x H with decide-is-positive-is-nonpositive-ℤ x
... | inl K = ex-falso (H K)
... | inr K = K
```

#### Nonnegativity is negated negativity

```agda
not-is-negative-is-nonnegative-ℤ :
  (x : ℤ) → is-nonnegative-ℤ x → ¬ (is-negative-ℤ x)
not-is-negative-is-nonnegative-ℤ x H K =
  not-is-positive-is-nonpositive-ℤ
    ( neg-ℤ x)
    ( is-nonpositive-neg-is-nonnegative-ℤ x H)
    ( is-positive-neg-is-negative-ℤ x K)

is-nonnegative-not-is-negative-ℤ :
  (x : ℤ) → ¬ (is-negative-ℤ x) → is-nonnegative-ℤ x
is-nonnegative-not-is-negative-ℤ x H with decide-is-negative-is-nonnegative-ℤ x
... | inl K = ex-falso (H K)
... | inr K = K
```
