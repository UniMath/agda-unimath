# Addition of positive, negative, nonnegative and nonpositive integers

```agda
module elementary-number-theory.addition-positive-and-negative-integers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integers
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

Addition of positive, negative, nonnegative and nonpositive integers follows the
following rules:

|     `p`     |     `q`     |  `p +ℤ q`   | operation           |
| :---------: | :---------: | :---------: | ------------------- |
|  positive   |  positive   |  positive   | `add-positive-ℤ`    |
|  positive   | nonnegative |  positive   |                     |
|  positive   |  negative   |     ??      |                     |
|  positive   | nonpositive |     ??      |                     |
| nonnegative | nonnegative | nonnegative | `add-nonnegative-ℤ` |
| nonnegative |  negative   |     ??      |                     |
| nonnegative | nonpositive |     ??      |                     |
|  negative   |  negative   |  negative   | `add-negative-ℤ`    |
|  negative   | nonpositive |  negative   |                     |
| nonpositive | nonpositive | nonpositive | `add-nonpositive-ℤ` |

where ?? marks undetermined cases.

## Properties

### The sum of two positive integers is positive

```agda
is-positive-add-positive-positive-ℤ :
  {x y : ℤ} → is-positive-ℤ x → is-positive-ℤ y → is-positive-ℤ (x +ℤ y)
is-positive-add-positive-positive-ℤ {inr (inr zero-ℕ)} {y} H K =
  is-positive-succ-is-positive-ℤ K
is-positive-add-positive-positive-ℤ {inr (inr (succ-ℕ x))} {y} H K =
  is-positive-succ-is-positive-ℤ
    ( is-positive-add-positive-positive-ℤ {inr (inr x)} H K)
```

### The sum of a nonnegative and a positive integer is nonnegative

```agda
is-positive-add-nonnegative-positive-ℤ :
  {x y : ℤ} → is-nonnegative-ℤ x → is-positive-ℤ y → is-positive-ℤ (x +ℤ y)
is-positive-add-nonnegative-positive-ℤ {inr (inl x)} {y} H H' = H'
is-positive-add-nonnegative-positive-ℤ {inr (inr x)} {y} H H' =
  is-positive-add-positive-positive-ℤ {inr (inr x)} {y} H H'
```

### The sum of a positive and a nonnegative integer is positive

```agda
is-positive-add-positive-nonnegative-ℤ :
  {x y : ℤ} → is-positive-ℤ x → is-nonnegative-ℤ y → is-positive-ℤ (x +ℤ y)
is-positive-add-positive-nonnegative-ℤ {x} {y} H H' =
  is-positive-eq-ℤ
    ( commutative-add-ℤ y x)
    ( is-positive-add-nonnegative-positive-ℤ H' H)
```

### The sum of two nonnegative integers is nonnegative

```agda
is-nonnegative-add-nonnegative-nonnegative-ℤ : {x y : ℤ} →
  is-nonnegative-ℤ x → is-nonnegative-ℤ y → is-nonnegative-ℤ (x +ℤ y)
is-nonnegative-add-nonnegative-nonnegative-ℤ {inr (inl x)} {y} H H' = H'
is-nonnegative-add-nonnegative-nonnegative-ℤ {inr (inr zero-ℕ)} {y} H H' =
  is-nonnegative-succ-is-nonnegative-ℤ H'
is-nonnegative-add-nonnegative-nonnegative-ℤ {inr (inr (succ-ℕ x))} {y} H H' =
  is-nonnegative-succ-is-nonnegative-ℤ
    ( is-nonnegative-add-nonnegative-nonnegative-ℤ {inr (inr x)} star H')
```

## Definitions

### Addition of positive integers

```agda
add-positive-ℤ : positive-ℤ → positive-ℤ → positive-ℤ
add-positive-ℤ (x , H) (y , K) =
  add-ℤ x y , is-positive-add-positive-positive-ℤ H K
```

### Addition of nonnegative integers

```agda
add-nonnegative-ℤ : nonnegative-ℤ → nonnegative-ℤ → nonnegative-ℤ
add-nonnegative-ℤ (x , H) (y , K) =
  add-ℤ x y , is-nonnegative-add-nonnegative-nonnegative-ℤ H K
```
