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
open import elementary-number-theory.positive-and-negative-integers
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
satisfies the following rules:

|     `p`     |     `q`     |  `p *ℤ q`   | operation           |
| :---------: | :---------: | :---------: | ------------------- |
|  positive   |  positive   |  positive   | `mul-positive-ℤ`    |
|  positive   | nonnegative | nonnegative |                     |
|  positive   |  negative   |  negative   |                     |
|  positive   | nonpositive | nonpositive |                     |
| nonnegative |  positive   | nonnegative |                     |
| nonnegative | nonnegative | nonnegative | `mul-nonnegative-ℤ` |
| nonnegative |  negative   | nonpositive |                     |
| nonnegative | nonpositive | nonpositive |                     |
|  negative   |  positive   |  negative   |                     |
|  negative   | nonnegative | nonpositive |                     |
|  negative   |  negative   |  positive   | `mul-negative-ℤ`    |
|  negative   | nonpositive | nonnegative |                     |
| nonpositive |  positive   | nonpositive |                     |
| nonpositive | nonnegative | nonpositive |                     |
| nonpositive |  negative   | nonpositive |                     |
| nonpositive | nonpositive | nonnegative | `mul-nonpositive-ℤ` |

As a consequence, multiplication by a positive integer preserves and reflects
strict inequality and multiplication by a nonpositive integer preserves and
reflects inequality.

## Properties

### Signed product rules

#### The product of two positive integers is positive

```agda
is-positive-mul-ℤ :
  {x y : ℤ} → is-positive-ℤ x → is-positive-ℤ y → is-positive-ℤ (x *ℤ y)
is-positive-mul-ℤ {inr (inr zero-ℕ)} {y} H K = K
is-positive-mul-ℤ {inr (inr (succ-ℕ x))} {y} H K =
  is-positive-add-ℤ K (is-positive-mul-ℤ {inr (inr x)} H K)
```

#### The product of a positive and a nonnegative integer is nonnegative

```agda
is-nonnegative-mul-positive-nonnegative-ℤ :
  {x y : ℤ} → is-positive-ℤ x → is-nonnegative-ℤ y → is-nonnegative-ℤ (x *ℤ y)
is-nonnegative-mul-positive-nonnegative-ℤ {inr (inr zero-ℕ)} {y} H K = K
is-nonnegative-mul-positive-nonnegative-ℤ {inr (inr (succ-ℕ x))} {y} H K =
  is-nonnegative-add-ℤ K
    ( is-nonnegative-mul-positive-nonnegative-ℤ {inr (inr x)} H K)
```

#### The product of a positive and a negative integer is negative

```agda
is-negative-mul-positive-negative-ℤ :
  {x y : ℤ} → is-positive-ℤ x → is-negative-ℤ y → is-negative-ℤ (x *ℤ y)
is-negative-mul-positive-negative-ℤ {x} {y} H K =
  is-negative-eq-ℤ
    ( neg-neg-ℤ (x *ℤ y))
    ( is-negative-neg-is-positive-ℤ
      ( is-positive-eq-ℤ
        ( right-negative-law-mul-ℤ x y)
        ( is-positive-mul-ℤ H (is-positive-neg-is-negative-ℤ K))))
```

#### The product of a positive and a nonpositive integer is nonpositive

```agda
is-nonpositive-mul-positive-nonpositive-ℤ :
  {x y : ℤ} → is-positive-ℤ x → is-nonpositive-ℤ y → is-nonpositive-ℤ (x *ℤ y)
is-nonpositive-mul-positive-nonpositive-ℤ {x} {y} H K =
  is-nonpositive-eq-ℤ
    ( neg-neg-ℤ (x *ℤ y))
    ( is-nonpositive-neg-is-nonnegative-ℤ
      ( is-nonnegative-eq-ℤ
        ( right-negative-law-mul-ℤ x y)
        ( is-nonnegative-mul-positive-nonnegative-ℤ H
          ( is-nonnegative-neg-is-nonpositive-ℤ K))))
```

#### The product of a nonnegative integer and a positive integer is nonnegative

```agda
is-nonnegative-mul-nonnegative-positive-ℤ :
  {x y : ℤ} → is-nonnegative-ℤ x → is-positive-ℤ y → is-nonnegative-ℤ (x *ℤ y)
is-nonnegative-mul-nonnegative-positive-ℤ {x} {y} H K =
  is-nonnegative-eq-ℤ
    ( commutative-mul-ℤ y x)
    ( is-nonnegative-mul-positive-nonnegative-ℤ K H)
```

#### The product of two nonnegative integers is nonnegative

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

#### The product of a nonnegative and a negative integer is nonpositive

```agda
is-nonpositive-mul-nonnegative-negative-ℤ :
  {x y : ℤ} → is-nonnegative-ℤ x → is-negative-ℤ y → is-nonpositive-ℤ (x *ℤ y)
is-nonpositive-mul-nonnegative-negative-ℤ {x} {y} H K =
  is-nonpositive-eq-ℤ
    ( neg-neg-ℤ (x *ℤ y))
    ( is-nonpositive-neg-is-nonnegative-ℤ
      ( is-nonnegative-eq-ℤ
        ( right-negative-law-mul-ℤ x y)
        ( is-nonnegative-mul-nonnegative-positive-ℤ H
          ( is-positive-neg-is-negative-ℤ K))))
```

#### The product of a nonnegative and a nonpositive integer is nonpositive

```agda
is-nonpositive-mul-nonnegative-nonpositive-ℤ :
  {x y : ℤ} →
  is-nonnegative-ℤ x → is-nonpositive-ℤ y → is-nonpositive-ℤ (x *ℤ y)
is-nonpositive-mul-nonnegative-nonpositive-ℤ {x} {y} H K =
  is-nonpositive-eq-ℤ
    ( neg-neg-ℤ (x *ℤ y))
    ( is-nonpositive-neg-is-nonnegative-ℤ
      ( is-nonnegative-eq-ℤ
        ( right-negative-law-mul-ℤ x y)
        ( is-nonnegative-mul-ℤ H
          ( is-nonnegative-neg-is-nonpositive-ℤ K))))
```

#### The product of a negative and a positive integer is negative

```agda
is-negative-mul-negative-positive-ℤ :
  {x y : ℤ} → is-negative-ℤ x → is-positive-ℤ y → is-negative-ℤ (x *ℤ y)
is-negative-mul-negative-positive-ℤ {x} {y} H K =
  is-negative-eq-ℤ
    ( commutative-mul-ℤ y x)
    ( is-negative-mul-positive-negative-ℤ K H)
```

#### The product of a negative and a nonnegative integer is nonpositive

```agda
is-nonpositive-mul-negative-nonnegative-ℤ :
  {x y : ℤ} → is-negative-ℤ x → is-nonnegative-ℤ y → is-nonpositive-ℤ (x *ℤ y)
is-nonpositive-mul-negative-nonnegative-ℤ {x} {y} H K =
  is-nonpositive-eq-ℤ
    ( commutative-mul-ℤ y x)
    ( is-nonpositive-mul-nonnegative-negative-ℤ K H)
```

#### The product of two negative integers is positive

```agda
is-positive-mul-negative-ℤ :
  {x y : ℤ} → is-negative-ℤ x → is-negative-ℤ y → is-positive-ℤ (x *ℤ y)
is-positive-mul-negative-ℤ {x} {y} H K =
  is-positive-eq-ℤ
    ( double-negative-law-mul-ℤ x y)
    ( is-positive-mul-ℤ
      ( is-positive-neg-is-negative-ℤ H)
      ( is-positive-neg-is-negative-ℤ K))
```

#### The product of a negative and a nonpositive integer is nonnegative

```agda
is-nonnegative-mul-negative-nonpositive-ℤ :
  {x y : ℤ} → is-negative-ℤ x → is-nonpositive-ℤ y → is-nonnegative-ℤ (x *ℤ y)
is-nonnegative-mul-negative-nonpositive-ℤ {x} {y} H K =
  is-nonnegative-eq-ℤ
    ( double-negative-law-mul-ℤ x y)
    ( is-nonnegative-mul-positive-nonnegative-ℤ
      ( is-positive-neg-is-negative-ℤ H)
      ( is-nonnegative-neg-is-nonpositive-ℤ K))
```

#### The product of a nonpositive and a positive integer is nonpositive

```agda
is-nonpositive-mul-nonpositive-positive-ℤ :
  {x y : ℤ} → is-nonpositive-ℤ x → is-positive-ℤ y → is-nonpositive-ℤ (x *ℤ y)
is-nonpositive-mul-nonpositive-positive-ℤ {x} {y} H K =
  is-nonpositive-eq-ℤ
    ( commutative-mul-ℤ y x)
    ( is-nonpositive-mul-positive-nonpositive-ℤ K H)
```

#### The product of a nonpositive and a nonnegative integer is nonpositive

```agda
is-nonpositive-mul-nonpositive-nonnegative-ℤ :
  {x y : ℤ} →
  is-nonpositive-ℤ x → is-nonnegative-ℤ y → is-nonpositive-ℤ (x *ℤ y)
is-nonpositive-mul-nonpositive-nonnegative-ℤ {x} {y} H K =
  is-nonpositive-eq-ℤ
    ( commutative-mul-ℤ y x)
    ( is-nonpositive-mul-nonnegative-nonpositive-ℤ K H)
```

#### The product of a nonpositive integer and a negative integer is nonnegative

```agda
is-nonnegative-mul-nonpositive-negative-ℤ :
  { x y : ℤ} → is-nonpositive-ℤ x → is-negative-ℤ y → is-nonnegative-ℤ (x *ℤ y)
is-nonnegative-mul-nonpositive-negative-ℤ {x} {y} H K =
  is-nonnegative-eq-ℤ
    ( commutative-mul-ℤ y x)
    ( is-nonnegative-mul-negative-nonpositive-ℤ K H)
```

#### The product of two nonpositive integers is nonnegative

```agda
is-nonnegative-mul-nonpositive-ℤ :
  {x y : ℤ} →
  is-nonpositive-ℤ x → is-nonpositive-ℤ y → is-nonnegative-ℤ (x *ℤ y)
is-nonnegative-mul-nonpositive-ℤ {x} {y} H K =
  is-nonnegative-eq-ℤ
    ( double-negative-law-mul-ℤ x y)
    ( is-nonnegative-mul-ℤ
      ( is-nonnegative-neg-is-nonpositive-ℤ H)
      ( is-nonnegative-neg-is-nonpositive-ℤ K))
```

### Rules for inequalities

#### Multiplication by a positive integer preserves the strict ordering

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

#### The left factor of a positive product with a positive right factor is positive

```agda
is-positive-left-factor-mul-ℤ :
  {x y : ℤ} → is-positive-ℤ (x *ℤ y) → is-positive-ℤ y → is-positive-ℤ x
is-positive-left-factor-mul-ℤ {inl x} {inr (inr y)} H K =
  is-positive-eq-ℤ (compute-mul-ℤ (inl x) (inr (inr y))) H
is-positive-left-factor-mul-ℤ {inr (inl star)} {inr (inr y)} H K =
  is-positive-eq-ℤ (compute-mul-ℤ zero-ℤ (inr (inr y))) H
is-positive-left-factor-mul-ℤ {inr (inr x)} {inr (inr y)} H K = star
```

#### The right factor of a positive product with a positive left factor is positive

```agda
is-positive-right-factor-mul-ℤ :
  {x y : ℤ} → is-positive-ℤ (x *ℤ y) → is-positive-ℤ x → is-positive-ℤ y
is-positive-right-factor-mul-ℤ {x} {y} H =
  is-positive-left-factor-mul-ℤ (is-positive-eq-ℤ (commutative-mul-ℤ x y) H)
```

#### Multiplication by a nonnegative integer preserves the ordering

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

#### The left factor of a nonnegative product with a nonnegative right factor is nonnegative

```agda
is-nonnegative-left-factor-mul-ℤ :
  {x y : ℤ} → is-nonnegative-ℤ (x *ℤ y) → is-positive-ℤ y → is-nonnegative-ℤ x
is-nonnegative-left-factor-mul-ℤ {inl x} {inr (inr y)} H K =
  ex-falso (is-nonnegative-eq-ℤ (compute-mul-ℤ (inl x) (inr (inr y))) H)
is-nonnegative-left-factor-mul-ℤ {inr x} {inr y} H K = star
```

#### The right factor of a nonnegative product with a nonnegative left factor is nonnegative

```agda
is-nonnegative-right-factor-mul-ℤ :
  {x y : ℤ} → is-nonnegative-ℤ (x *ℤ y) → is-positive-ℤ x → is-nonnegative-ℤ y
is-nonnegative-right-factor-mul-ℤ {x} {y} H =
  is-nonnegative-left-factor-mul-ℤ
    ( is-nonnegative-eq-ℤ (commutative-mul-ℤ x y) H)
```

## Definitions

### Multiplication of positive integers

```agda
mul-positive-ℤ : positive-ℤ → positive-ℤ → positive-ℤ
mul-positive-ℤ (x , H) (y , K) = mul-ℤ x y , is-positive-mul-ℤ H K
```

### Multiplication of nonnegative integers

```agda
mul-nonnegative-ℤ : nonnegative-ℤ → nonnegative-ℤ → nonnegative-ℤ
mul-nonnegative-ℤ (x , H) (y , K) = mul-ℤ x y , is-nonnegative-mul-ℤ H K
```

### Multiplication of negative integers

```agda
mul-negative-ℤ : negative-ℤ → negative-ℤ → positive-ℤ
mul-negative-ℤ (x , H) (y , K) = mul-ℤ x y , is-positive-mul-negative-ℤ H K
```

### Multiplication of nonpositive integers

```agda
mul-nonpositive-ℤ : nonpositive-ℤ → nonpositive-ℤ → nonnegative-ℤ
mul-nonpositive-ℤ (x , H) (y , K) =
  mul-ℤ x y , is-nonnegative-mul-nonpositive-ℤ H K
```
