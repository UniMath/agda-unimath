# Multiplication of positive, negative, nonnegative and nonpositive integers

```agda
module elementary-number-theory.multiplication-positive-and-negative-integers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-positive-and-negative-integers
open import elementary-number-theory.inequality-integers
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integers
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

Multiplication of positive, negative, nonnegative and nonpositive integers
follows the following rules:

|     `p`     |     `q`     |  `p *ℤ q`   | operation           |
| :---------: | :---------: | :---------: | ------------------- |
|  positive   |  positive   |  positive   | `mul-positive-ℤ`    |
|  positive   | nonnegative | nonnegative |                     |
|  positive   |  negative   |  negative   |                     |
|  positive   | nonpositive | nonpositive |                     |
| nonnegative | nonnegative | nonnegative | `mul-nonnegative-ℤ` |
| nonnegative |  negative   | nonpositive |                     |
| nonnegative | nonpositive | nonpositive |                     |
|  negative   |  negative   |  positive   | `mul-negative-ℤ`    |
|  negative   | nonpositive | nonnegative |                     |
| nonpositive | nonpositive | nonnegative | `mul-nonpositive-ℤ` |

## Properties

### The product of two positive integers is positive

```agda
is-positive-mul-ℤ :
  {x y : ℤ} → is-positive-ℤ x → is-positive-ℤ y → is-positive-ℤ (x *ℤ y)
is-positive-mul-ℤ {inr (inr zero-ℕ)} {y} H K = K
is-positive-mul-ℤ {inr (inr (succ-ℕ x))} {y} H K =
  is-positive-add-ℤ {y} K
    ( is-positive-mul-ℤ {inr (inr x)} {y} H K)
```

### The product of two nonnegative integers is nonnegative

```agda
is-nonnegative-mul-ℤ :
  {x y : ℤ} →
  is-nonnegative-ℤ x → is-nonnegative-ℤ y → is-nonnegative-ℤ (x *ℤ y)
is-nonnegative-mul-ℤ {inr (inl star)} {y} H K = star
is-nonnegative-mul-ℤ {inr (inr x)} {inr (inl star)} H K =
  is-nonnegative-eq-ℤ (inv (right-zero-law-mul-ℤ (inr (inr x)))) star
is-nonnegative-mul-ℤ {inr (inr x)} {inr (inr y)} H K =
  is-nonnegative-eq-ℤ (inv (compute-mul-ℤ (inr (inr x)) (inr (inr y)))) star
```

### The left factor of a positive product with a positive right factor is positive

```agda
is-positive-left-factor-mul-ℤ :
  {x y : ℤ} → is-positive-ℤ (x *ℤ y) → is-positive-ℤ y → is-positive-ℤ x
is-positive-left-factor-mul-ℤ {inl x} {inr (inr y)} H K =
  is-positive-eq-ℤ (compute-mul-ℤ (inl x) (inr (inr y))) H
is-positive-left-factor-mul-ℤ {inr (inl star)} {inr (inr y)} H K =
  is-positive-eq-ℤ (compute-mul-ℤ zero-ℤ (inr (inr y))) H
is-positive-left-factor-mul-ℤ {inr (inr x)} {inr (inr y)} H K = star
```

### The right factor of a positive product with a positive left factor is positive

```agda
is-positive-right-factor-mul-ℤ :
  {x y : ℤ} → is-positive-ℤ (x *ℤ y) → is-positive-ℤ x → is-positive-ℤ y
is-positive-right-factor-mul-ℤ {x} {y} H =
  is-positive-left-factor-mul-ℤ (is-positive-eq-ℤ (commutative-mul-ℤ x y) H)
```

### Multiplication by a positive integer preserves the strict ordering

```agda
preserves-le-left-mul-ℤ :
  {x y z : ℤ} → is-positive-ℤ z → le-ℤ x y → le-ℤ (x *ℤ z) (y *ℤ z)
preserves-le-left-mul-ℤ {x} {y} {z} H p =
  is-positive-eq-ℤ
    ( inv (linear-diff-right-mul-ℤ y x z))
    ( is-positive-mul-ℤ p H)

preserves-le-right-mul-ℤ :
  {x y z : ℤ} → is-positive-ℤ z → le-ℤ x y → le-ℤ (z *ℤ x) (z *ℤ y)
preserves-le-right-mul-ℤ {x} {y} {z} H p =
  is-positive-eq-ℤ
    ( inv (linear-diff-left-mul-ℤ z y x))
    ( is-positive-mul-ℤ H p)
```

### The left factor of a nonnegative product with a nonnegative right factor is nonnegative

```agda
is-nonnegative-left-factor-mul-ℤ :
  {x y : ℤ} → is-nonnegative-ℤ (x *ℤ y) → is-positive-ℤ y → is-nonnegative-ℤ x
is-nonnegative-left-factor-mul-ℤ {inl x} {inr (inr y)} H K =
  ex-falso (is-nonnegative-eq-ℤ (compute-mul-ℤ (inl x) (inr (inr y))) H)
is-nonnegative-left-factor-mul-ℤ {inr x} {inr y} H K = star
```

### The right factor of a nonnegative product with a nonnegative left factor is nonnegative

```agda
is-nonnegative-right-factor-mul-ℤ :
  {x y : ℤ} → is-nonnegative-ℤ (x *ℤ y) → is-positive-ℤ x → is-nonnegative-ℤ y
is-nonnegative-right-factor-mul-ℤ {x} {y} H =
  is-nonnegative-left-factor-mul-ℤ
    ( is-nonnegative-eq-ℤ (commutative-mul-ℤ x y) H)
```

### Multiplication by a nonnegative integer preserves the ordering

```agda
preserves-leq-left-mul-ℤ :
  {x y z : ℤ} → is-nonnegative-ℤ z → leq-ℤ x y → leq-ℤ (z *ℤ x) (z *ℤ y)
preserves-leq-left-mul-ℤ {x} {y} {inr (inl star)} star K = star
preserves-leq-left-mul-ℤ {x} {y} {inr (inr zero-ℕ)} star K = K
preserves-leq-left-mul-ℤ {x} {y} {inr (inr (succ-ℕ n))} star K =
  preserves-leq-add-ℤ {x} {y}
    ( K)
    ( preserves-leq-left-mul-ℤ {x} {y} {inr (inr n)} star K)

preserves-leq-right-mul-ℤ :
  {x y z : ℤ} → is-nonnegative-ℤ z → leq-ℤ x y → leq-ℤ (x *ℤ z) (y *ℤ z)
preserves-leq-right-mul-ℤ {x} {y} {z} H K =
  concatenate-eq-leq-eq-ℤ
    ( commutative-mul-ℤ x z)
    ( preserves-leq-left-mul-ℤ H K)
    ( commutative-mul-ℤ z y)
```

## Definitions

### Multiplication of positive integers

```agda
mul-positive-ℤ : positive-ℤ → positive-ℤ → positive-ℤ
mul-positive-ℤ (x , H) (y , K) = mul-ℤ x y , is-positive-mul-ℤ H K

compute-mul-positive-ℤ :
  {x y : positive-ℤ} →
  Id
    ( mul-ℤ (int-positive-ℤ x) (int-positive-ℤ y))
    ( int-positive-ℤ (mul-positive-ℤ x y))
compute-mul-positive-ℤ {x , H} {y , K} = refl
```

### Multiplication of nonnegative integers

```agda
mul-nonnegative-ℤ : nonnegative-ℤ → nonnegative-ℤ → nonnegative-ℤ
mul-nonnegative-ℤ (x , H) (y , K) = mul-ℤ x y , is-nonnegative-mul-ℤ H K
```
