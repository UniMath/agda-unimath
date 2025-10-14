# The integers

```agda
module elementary-number-theory.integers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.equality-natural-numbers
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
open import foundation.involutions
open import foundation.negated-equality
open import foundation.negation
open import foundation.propositions
open import foundation.retractions
open import foundation.sections
open import foundation.sets
open import foundation.unit-type
open import foundation.universe-levels

open import structured-types.types-equipped-with-endomorphisms
```

</details>

## Idea

The type of {{#concept "integers" WD="integer" WDID=Q12503 Agda=ℤ}} is an
extension of the type of
[natural numbers](elementary-number-theory.natural-numbers.md) including
negative whole numbers.

## Definitions

### The type of integers

```agda
ℤ : UU lzero
ℤ = ℕ + (unit + ℕ)

{-# BUILTIN INTEGER ℤ #-}
```

### Inclusion of the negative integers

```agda
in-neg-ℤ : ℕ → ℤ
in-neg-ℤ n = inl n

neg-one-ℤ : ℤ
neg-one-ℤ = in-neg-ℤ zero-ℕ

is-neg-one-ℤ : ℤ → UU lzero
is-neg-one-ℤ x = (x ＝ neg-one-ℤ)
```

### Zero

```agda
zero-ℤ : ℤ
zero-ℤ = inr (inl star)

is-zero-ℤ : ℤ → UU lzero
is-zero-ℤ x = (x ＝ zero-ℤ)

eq-is-zero-ℤ : {a b : ℤ} → is-zero-ℤ a → is-zero-ℤ b → a ＝ b
eq-is-zero-ℤ {a} {b} H K = H ∙ inv K
```

### Inclusion of the positive integers

```agda
in-pos-ℤ : ℕ → ℤ
in-pos-ℤ n = inr (inr n)

one-ℤ : ℤ
one-ℤ = in-pos-ℤ zero-ℕ

is-one-ℤ : ℤ → UU lzero
is-one-ℤ x = (x ＝ one-ℤ)
```

### Inclusion of the natural numbers

```agda
int-ℕ : ℕ → ℤ
int-ℕ zero-ℕ = zero-ℤ
int-ℕ (succ-ℕ n) = in-pos-ℤ n

is-injective-int-ℕ : is-injective int-ℕ
is-injective-int-ℕ {zero-ℕ} {zero-ℕ} refl = refl
is-injective-int-ℕ {succ-ℕ x} {succ-ℕ y} refl = refl
```

### Induction principle on the type of integers

```agda
ind-ℤ :
  {l : Level} (P : ℤ → UU l) →
  P neg-one-ℤ → ((n : ℕ) → P (inl n) → P (inl (succ-ℕ n))) →
  P zero-ℤ →
  P one-ℤ → ((n : ℕ) → P (inr (inr (n))) → P (inr (inr (succ-ℕ n)))) →
  (k : ℤ) → P k
ind-ℤ P p-1 p-S p0 p1 pS (inl zero-ℕ) = p-1
ind-ℤ P p-1 p-S p0 p1 pS (inl (succ-ℕ x)) =
  p-S x (ind-ℤ P p-1 p-S p0 p1 pS (inl x))
ind-ℤ P p-1 p-S p0 p1 pS (inr (inl star)) = p0
ind-ℤ P p-1 p-S p0 p1 pS (inr (inr zero-ℕ)) = p1
ind-ℤ P p-1 p-S p0 p1 pS (inr (inr (succ-ℕ x))) =
  pS x (ind-ℤ P p-1 p-S p0 p1 pS (inr (inr (x))))
```

### The successor and predecessor functions on ℤ

```agda
succ-ℤ : ℤ → ℤ
succ-ℤ (inl zero-ℕ) = zero-ℤ
succ-ℤ (inl (succ-ℕ x)) = inl x
succ-ℤ (inr (inl star)) = one-ℤ
succ-ℤ (inr (inr x)) = inr (inr (succ-ℕ x))

pred-ℤ : ℤ → ℤ
pred-ℤ (inl x) = inl (succ-ℕ x)
pred-ℤ (inr (inl star)) = inl zero-ℕ
pred-ℤ (inr (inr zero-ℕ)) = inr (inl star)
pred-ℤ (inr (inr (succ-ℕ x))) = inr (inr x)

ℤ-Type-With-Endomorphism : Type-With-Endomorphism lzero
pr1 ℤ-Type-With-Endomorphism = ℤ
pr2 ℤ-Type-With-Endomorphism = succ-ℤ
```

### The negative of an integer

```agda
neg-ℤ : ℤ → ℤ
neg-ℤ (inl x) = inr (inr x)
neg-ℤ (inr (inl star)) = inr (inl star)
neg-ℤ (inr (inr x)) = inl x
```

## Properties

### The type of integers is a set

```agda
abstract
  is-set-ℤ : is-set ℤ
  is-set-ℤ = is-set-coproduct is-set-ℕ (is-set-coproduct is-set-unit is-set-ℕ)

ℤ-Set : Set lzero
pr1 ℤ-Set = ℤ
pr2 ℤ-Set = is-set-ℤ
```

### The successor and predecessor functions on ℤ are mutual inverses

```agda
abstract
  is-retraction-pred-ℤ : is-retraction succ-ℤ pred-ℤ
  is-retraction-pred-ℤ (inl zero-ℕ) = refl
  is-retraction-pred-ℤ (inl (succ-ℕ x)) = refl
  is-retraction-pred-ℤ (inr (inl _)) = refl
  is-retraction-pred-ℤ (inr (inr zero-ℕ)) = refl
  is-retraction-pred-ℤ (inr (inr (succ-ℕ x))) = refl

  is-section-pred-ℤ : is-section succ-ℤ pred-ℤ
  is-section-pred-ℤ (inl zero-ℕ) = refl
  is-section-pred-ℤ (inl (succ-ℕ x)) = refl
  is-section-pred-ℤ (inr (inl _)) = refl
  is-section-pred-ℤ (inr (inr zero-ℕ)) = refl
  is-section-pred-ℤ (inr (inr (succ-ℕ x))) = refl

abstract
  is-equiv-succ-ℤ : is-equiv succ-ℤ
  is-equiv-succ-ℤ =
    is-equiv-is-invertible pred-ℤ is-section-pred-ℤ is-retraction-pred-ℤ

equiv-succ-ℤ : ℤ ≃ ℤ
pr1 equiv-succ-ℤ = succ-ℤ
pr2 equiv-succ-ℤ = is-equiv-succ-ℤ

abstract
  is-equiv-pred-ℤ : is-equiv pred-ℤ
  is-equiv-pred-ℤ =
    is-equiv-is-invertible succ-ℤ is-retraction-pred-ℤ is-section-pred-ℤ

equiv-pred-ℤ : ℤ ≃ ℤ
pr1 equiv-pred-ℤ = pred-ℤ
pr2 equiv-pred-ℤ = is-equiv-pred-ℤ
```

### The successor function on ℤ is injective and has no fixed points

```agda
abstract
  is-injective-succ-ℤ : is-injective succ-ℤ
  is-injective-succ-ℤ = is-injective-is-equiv is-equiv-succ-ℤ

  has-no-fixed-points-succ-ℤ : (x : ℤ) → succ-ℤ x ≠ x
  has-no-fixed-points-succ-ℤ (inl zero-ℕ) ()
  has-no-fixed-points-succ-ℤ (inl (succ-ℕ x)) ()
  has-no-fixed-points-succ-ℤ (inr (inl star)) ()
```

### The negation function is an involution

```agda
abstract
  neg-neg-ℤ : neg-ℤ ∘ neg-ℤ ~ id
  neg-neg-ℤ (inl n) = refl
  neg-neg-ℤ (inr (inl star)) = refl
  neg-neg-ℤ (inr (inr n)) = refl
```

### The negation function is an equivalence

```agda
abstract
  is-equiv-neg-ℤ : is-equiv neg-ℤ
  is-equiv-neg-ℤ = is-equiv-is-involution neg-neg-ℤ

equiv-neg-ℤ : ℤ ≃ ℤ
pr1 equiv-neg-ℤ = neg-ℤ
pr2 equiv-neg-ℤ = is-equiv-neg-ℤ
```

### The negation function is an embedding

```agda
abstract
  is-emb-neg-ℤ : is-emb neg-ℤ
  is-emb-neg-ℤ = is-emb-is-equiv is-equiv-neg-ℤ

emb-neg-ℤ : ℤ ↪ ℤ
pr1 emb-neg-ℤ = neg-ℤ
pr2 emb-neg-ℤ = is-emb-neg-ℤ
```

### The negation of the predecessor of `x` is the successor of the negation of `x`

```agda
abstract
  neg-pred-ℤ : (k : ℤ) → neg-ℤ (pred-ℤ k) ＝ succ-ℤ (neg-ℤ k)
  neg-pred-ℤ (inl x) = refl
  neg-pred-ℤ (inr (inl star)) = refl
  neg-pred-ℤ (inr (inr zero-ℕ)) = refl
  neg-pred-ℤ (inr (inr (succ-ℕ x))) = refl
```

### The negation of the successor of `x` is the predecessor of the negation of `x`

```agda
abstract
  neg-succ-ℤ : (x : ℤ) → neg-ℤ (succ-ℤ x) ＝ pred-ℤ (neg-ℤ x)
  neg-succ-ℤ (inl zero-ℕ) = refl
  neg-succ-ℤ (inl (succ-ℕ x)) = refl
  neg-succ-ℤ (inr (inl star)) = refl
  neg-succ-ℤ (inr (inr x)) = refl
```

### The predecessor of the negation of `x` is the negation of the successor of `x`

```agda
abstract
  pred-neg-ℤ :
    (k : ℤ) → pred-ℤ (neg-ℤ k) ＝ neg-ℤ (succ-ℤ k)
  pred-neg-ℤ (inl zero-ℕ) = refl
  pred-neg-ℤ (inl (succ-ℕ x)) = refl
  pred-neg-ℤ (inr (inl star)) = refl
  pred-neg-ℤ (inr (inr x)) = refl
```

### The negation function is injective

```agda
abstract
  is-injective-neg-ℤ : is-injective neg-ℤ
  is-injective-neg-ℤ = is-injective-is-equiv is-equiv-neg-ℤ
```

### The integer successor of a natural number is the successor of the natural number

```agda
abstract
  succ-int-ℕ : (x : ℕ) → succ-ℤ (int-ℕ x) ＝ int-ℕ (succ-ℕ x)
  succ-int-ℕ zero-ℕ = refl
  succ-int-ℕ (succ-ℕ x) = refl
```

### An integer is zero if its negative is zero

```agda
abstract
  is-zero-is-zero-neg-ℤ : (x : ℤ) → is-zero-ℤ (neg-ℤ x) → is-zero-ℤ x
  is-zero-is-zero-neg-ℤ (inr (inl star)) H = refl
```

## See also

- We show in
  [`structured-types.initial-pointed-type-equipped-with-automorphism`](structured-types.initial-pointed-type-equipped-with-automorphism.md)
  that ℤ is the initial pointed type equipped with an automorphism.
- The group of integers is constructed in
  [`elementary-number-theory.group-of-integers`](elementary-number-theory.group-of-integers.md).
