# The signed integers

```agda
module elementary-number-theory.signed-integers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.integers
open import elementary-number-theory.natural-numbers

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

An integer can be called negative, nonpositive, nonnegative or positive
depending its position with respect to `neg-one-ℤ`, `zero-ℤ` and `one-ℤ`.

## Definitions

### Nonnegative integers

```agda
subtype-nonnegative-ℤ : subtype lzero ℤ
subtype-nonnegative-ℤ (inl x) = empty-Prop
subtype-nonnegative-ℤ (inr x) = unit-Prop

*is-nonnegative-ℤ : ℤ → UU lzero
*is-nonnegative-ℤ = is-in-subtype subtype-nonnegative-ℤ

*nonnegative-ℤ : UU lzero
*nonnegative-ℤ = type-subtype subtype-nonnegative-ℤ

module _
  (p : *nonnegative-ℤ)
  where

  *int-nonnegative-ℤ : ℤ
  *int-nonnegative-ℤ = pr1 p

  *is-nonnegative-int-nonnegative-ℤ : *is-nonnegative-ℤ *int-nonnegative-ℤ
  *is-nonnegative-int-nonnegative-ℤ = pr2 p
```

### Positive integers

```agda
subtype-positive-ℤ : subtype lzero ℤ
subtype-positive-ℤ (inl x) = empty-Prop
subtype-positive-ℤ (inr (inl x)) = empty-Prop
subtype-positive-ℤ (inr (inr x)) = unit-Prop

*is-positive-ℤ : ℤ → UU lzero
*is-positive-ℤ = is-in-subtype subtype-positive-ℤ

*positive-ℤ : UU lzero
*positive-ℤ = type-subtype subtype-positive-ℤ

module _
  (p : *positive-ℤ)
  where

  *int-positive-ℤ : ℤ
  *int-positive-ℤ = pr1 p

  *is-positive-int-positive-ℤ : *is-positive-ℤ *int-positive-ℤ
  *is-positive-int-positive-ℤ = pr2 p
```

### Nonnpositive integers

```agda
subtype-nonpositive-ℤ : subtype lzero ℤ
subtype-nonpositive-ℤ = subtype-nonnegative-ℤ ∘ neg-ℤ

*is-nonpositive-ℤ : ℤ → UU lzero
*is-nonpositive-ℤ = is-in-subtype subtype-nonpositive-ℤ

nonpositive-ℤ : UU lzero
nonpositive-ℤ = type-subtype subtype-nonpositive-ℤ

module _
  (p : nonpositive-ℤ)
  where

  int-nonpositive-ℤ : ℤ
  int-nonpositive-ℤ = pr1 p

  is-nonpositive-int-nonpositive-ℤ : *is-nonpositive-ℤ int-nonpositive-ℤ
  is-nonpositive-int-nonpositive-ℤ = pr2 p
```

### Negative integers

```agda
subtype-negative-ℤ : subtype lzero ℤ
subtype-negative-ℤ = subtype-positive-ℤ ∘ neg-ℤ

is-negative-ℤ : ℤ → UU lzero
is-negative-ℤ = is-in-subtype subtype-negative-ℤ

negative-ℤ : UU lzero
negative-ℤ = type-subtype subtype-negative-ℤ

module _
  (p : negative-ℤ)
  where

  int-negative-ℤ : ℤ
  int-negative-ℤ = pr1 p

  is-negative-int-negative-ℤ : is-negative-ℤ int-negative-ℤ
  is-negative-int-negative-ℤ = pr2 p
```

### Signed integer constants

The signed image of the integer constants `zero-ℤ` , `one-ℤ` nad `neg-one-ℤ`

#### Nonnegative constants

```agda
nonnegative-zero-ℤ : *nonnegative-ℤ
nonnegative-zero-ℤ = zero-ℤ , star

nonnegative-one-ℤ : *nonnegative-ℤ
nonnegative-one-ℤ = one-ℤ , star
```

#### Positive constants

```agda
*positive-one-ℤ : *positive-ℤ
*positive-one-ℤ = one-ℤ , star
```

#### Nonpositive constants

```agda
nonpositive-zero-ℤ : nonpositive-ℤ
nonpositive-zero-ℤ = zero-ℤ , star

nonpositive-neg-one-ℤ : nonpositive-ℤ
nonpositive-neg-one-ℤ = neg-one-ℤ , star
```

#### Negative constants

```agda
negative-neg-one-ℤ : negative-ℤ
negative-neg-one-ℤ = neg-one-ℤ , star
```

## Properties

### The only nonnegative and nonpositive integer is `zero-ℤ`

```agda
is-zero-is-nonnegative-is-nonpositive-ℤ :
  (x : ℤ) → *is-nonnegative-ℤ x → *is-nonpositive-ℤ x → is-zero-ℤ x
is-zero-is-nonnegative-is-nonpositive-ℤ (inr (inl x)) H K = refl
```

### A nonzero integer is either negative or positive

```agda
decide-sign-nonzero-ℤ :
  (x : ℤ) → x ≠ zero-ℤ → is-negative-ℤ x + *is-positive-ℤ x
decide-sign-nonzero-ℤ (inl x) H = inl star
decide-sign-nonzero-ℤ (inr (inl x)) H = ex-falso (H refl)
decide-sign-nonzero-ℤ (inr (inr x)) H = inr star
```

### Positive integers are nonnegative

```agda
*is-nonnegative-is-positive-ℤ : (x : ℤ) → *is-positive-ℤ x → *is-nonnegative-ℤ x
*is-nonnegative-is-positive-ℤ (inr (inr x)) H = H
```

### Negative integers are nonpositive

```agda
is-nonpositive-is-negative-ℤ : (x : ℤ) → is-negative-ℤ x → *is-nonpositive-ℤ x
is-nonpositive-is-negative-ℤ x = *is-nonnegative-is-positive-ℤ (neg-ℤ x)
```

### The successor of a nonnegative integer is positive

```agda
*is-positive-succ-ℤ : (x : ℤ) → *is-nonnegative-ℤ x → *is-positive-ℤ (succ-ℤ x)
*is-positive-succ-ℤ (inr (inl x)) H = star
*is-positive-succ-ℤ (inr (inr x)) H = star
```

### The predecessor of a positive integer is nonnegative

```agda
is-nonnegative-pred-ℤ :
  (x : ℤ) → *is-positive-ℤ x → *is-nonnegative-ℤ (pred-ℤ x)
is-nonnegative-pred-ℤ (inr (inr zero-ℕ)) H = star
is-nonnegative-pred-ℤ (inr (inr (succ-ℕ x))) H = star
```

### The predecessor of a nonnpositive integer is negative

-- TODO

### The successor of a negative integer is nonpositive

-- TODO

### The negative of a nonnegative integer is nonpositive

```agda
is-nonpositive-neg-is-nonnegative-ℤ :
  (x : ℤ) → *is-nonnegative-ℤ x → *is-nonpositive-ℤ (neg-ℤ x)
is-nonpositive-neg-is-nonnegative-ℤ x = tr *is-nonnegative-ℤ (inv (neg-neg-ℤ x))
```

Remark : the converse is true by definition

### The negative of a positive integer is negative

```agda
is-negative-neg-is-positive-ℤ :
  (x : ℤ) → *is-positive-ℤ x → is-negative-ℤ (neg-ℤ x)
is-negative-neg-is-positive-ℤ x = tr *is-positive-ℤ (inv (neg-neg-ℤ x))
```

Remark : the converse is true by definition

### An integer is positive or nonpositive

```agda
decide-is-positive-is-nonpositive-ℤ :
  (x : ℤ) → *is-positive-ℤ x + *is-nonpositive-ℤ x
decide-is-positive-is-nonpositive-ℤ (inl x) = inr star
decide-is-positive-is-nonpositive-ℤ (inr (inl x)) = inr star
decide-is-positive-is-nonpositive-ℤ (inr (inr x)) = inl star
```

### An integer is negative or nonnegative

```agda
decide-is-negative-is-nonnegative-ℤ :
  (x : ℤ) → is-negative-ℤ x + *is-nonnegative-ℤ x
decide-is-negative-is-nonnegative-ℤ x
  with decide-is-positive-is-nonpositive-ℤ (neg-ℤ x)
... | inl p = inl p
... | inr q = inr (tr *is-nonnegative-ℤ (neg-neg-ℤ x) q)
```

### Nonpositivity is negated positivity

```agda
not-is-positive-is-nonpositive-ℤ :
  (x : ℤ) → *is-nonpositive-ℤ x → ¬ (*is-positive-ℤ x)
not-is-positive-is-nonpositive-ℤ (inr (inl x)) _ q = q
not-is-positive-is-nonpositive-ℤ (inr (inr x)) p _ = p

*is-nonpositive-not-is-positive-ℤ :
  (x : ℤ) → ¬ (*is-positive-ℤ x) → *is-nonpositive-ℤ x
*is-nonpositive-not-is-positive-ℤ x H with decide-is-positive-is-nonpositive-ℤ x
... | inl K = ex-falso (H K)
... | inr K = K
```

### Nonnegativity is negated negativity

```agda
not-is-negative-is-nonnegative-ℤ :
  (x : ℤ) → *is-nonnegative-ℤ x → ¬ (is-negative-ℤ x)
not-is-negative-is-nonnegative-ℤ x H =
  not-is-positive-is-nonpositive-ℤ
    ( neg-ℤ x)
    ( is-nonpositive-neg-is-nonnegative-ℤ x H)

is-nonnegative-not-is-negative-ℤ :
  (x : ℤ) → ¬ (is-negative-ℤ x) → *is-nonnegative-ℤ x
is-nonnegative-not-is-negative-ℤ x H with decide-is-negative-is-nonnegative-ℤ x
... | inl K = ex-falso (H K)
... | inr K = K
```

### The integer image of a natural number is nonnegative

```agda
*is-nonnegative-int-ℕ : (n : ℕ) → *is-nonnegative-ℤ (int-ℕ n)
*is-nonnegative-int-ℕ zero-ℕ = star
*is-nonnegative-int-ℕ (succ-ℕ n) = star
```

### The canonical equivalence between natural numbers and nonnegative integers

```agda
*nonnegative-int-ℕ : ℕ → *nonnegative-ℤ
*nonnegative-int-ℕ n = int-ℕ n , *is-nonnegative-int-ℕ n

*nat-nonnegative-ℤ : *nonnegative-ℤ → ℕ
*nat-nonnegative-ℤ (inr (inl x) , H) = zero-ℕ
*nat-nonnegative-ℤ (inr (inr x) , H) = succ-ℕ x
```

-- TODO
