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
open import elementary-number-theory.positive-and-negative-integers
open import elementary-number-theory.positive-integers

open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.unit-type
```

</details>

## Idea

When we have information about the sign of the summands, we can in many cases
deduce the sign of their sum too. The table below tabulates all such cases and
displays the corresponding Agda definition.

|     `p`     |     `q`     |  `p +ℤ q`   | operation           |
| :---------: | :---------: | :---------: | ------------------- |
|  positive   |  positive   |  positive   | `add-positive-ℤ`    |
|  positive   | nonnegative |  positive   |                     |
|  positive   |  negative   |             |                     |
|  positive   | nonpositive |             |                     |
| nonnegative |  positive   |  positive   |                     |
| nonnegative | nonnegative | nonnegative | `add-nonnegative-ℤ` |
| nonnegative |  negative   |             |                     |
| nonnegative | nonpositive |             |                     |
|  negative   |  positive   |             |                     |
|  negative   | nonnegative |             |                     |
|  negative   |  negative   |  negative   | `add-negative-ℤ`    |
|  negative   | nonpositive |  negative   |                     |
| nonpositive |  positive   |             |                     |
| nonpositive | nonnegative |             |                     |
| nonpositive |  negative   |  negative   |                     |
| nonpositive | nonpositive | nonpositive | `add-nonpositive-ℤ` |

## Lemmas

### The sum of two positive integers is positive

```agda
abstract
  is-positive-add-ℤ :
    {x y : ℤ} → is-positive-ℤ x → is-positive-ℤ y → is-positive-ℤ (x +ℤ y)
  is-positive-add-ℤ {inr (inr zero-ℕ)} {y} H K =
    is-positive-succ-is-positive-ℤ K
  is-positive-add-ℤ {inr (inr (succ-ℕ x))} {y} H K =
    is-positive-succ-is-positive-ℤ
      ( is-positive-add-ℤ {inr (inr x)} H K)
```

### The sum of a positive and a nonnegative integer is positive

```agda
abstract
  is-positive-add-positive-nonnegative-ℤ :
    {x y : ℤ} → is-positive-ℤ x → is-nonnegative-ℤ y → is-positive-ℤ (x +ℤ y)
  is-positive-add-positive-nonnegative-ℤ {inr (inr zero-ℕ)} {y} H K =
    is-positive-succ-is-nonnegative-ℤ K
  is-positive-add-positive-nonnegative-ℤ {inr (inr (succ-ℕ x))} {y} H K =
    is-positive-succ-is-positive-ℤ
      ( is-positive-add-positive-nonnegative-ℤ {inr (inr x)} H K)
```

### The sum of a nonnegative and a positive integer is positive

```agda
abstract
  is-positive-add-nonnegative-positive-ℤ :
    {x y : ℤ} → is-nonnegative-ℤ x → is-positive-ℤ y → is-positive-ℤ (x +ℤ y)
  is-positive-add-nonnegative-positive-ℤ {x} {y} H K =
    is-positive-eq-ℤ
      ( commutative-add-ℤ y x)
      ( is-positive-add-positive-nonnegative-ℤ K H)
```

### The sum of two nonnegative integers is nonnegative

```agda
abstract
  is-nonnegative-add-ℤ :
    {x y : ℤ} →
    is-nonnegative-ℤ x → is-nonnegative-ℤ y → is-nonnegative-ℤ (x +ℤ y)
  is-nonnegative-add-ℤ {inr (inl x)} {y} H K = K
  is-nonnegative-add-ℤ {inr (inr zero-ℕ)} {y} H K =
    is-nonnegative-succ-is-nonnegative-ℤ K
  is-nonnegative-add-ℤ {inr (inr (succ-ℕ x))} {y} H K =
    is-nonnegative-succ-is-nonnegative-ℤ
      ( is-nonnegative-add-ℤ {inr (inr x)} star K)
```

### The sum of two negative integers is negative

```agda
abstract
  is-negative-add-ℤ :
    {x y : ℤ} → is-negative-ℤ x → is-negative-ℤ y → is-negative-ℤ (x +ℤ y)
  is-negative-add-ℤ {x} {y} H K =
    is-negative-eq-ℤ
      ( neg-neg-ℤ (x +ℤ y))
      ( is-negative-neg-is-positive-ℤ
        ( is-positive-eq-ℤ
          ( inv (distributive-neg-add-ℤ x y))
          ( is-positive-add-ℤ
            ( is-positive-neg-is-negative-ℤ H)
            ( is-positive-neg-is-negative-ℤ K))))
```

### The sum of a negative and a nonpositive integer is negative

```agda
abstract
  is-negative-add-negative-nonnegative-ℤ :
    {x y : ℤ} → is-negative-ℤ x → is-nonpositive-ℤ y → is-negative-ℤ (x +ℤ y)
  is-negative-add-negative-nonnegative-ℤ {x} {y} H K =
    is-negative-eq-ℤ
      ( neg-neg-ℤ (x +ℤ y))
      ( is-negative-neg-is-positive-ℤ
        ( is-positive-eq-ℤ
          ( inv (distributive-neg-add-ℤ x y))
          ( is-positive-add-positive-nonnegative-ℤ
            ( is-positive-neg-is-negative-ℤ H)
            ( is-nonnegative-neg-is-nonpositive-ℤ K))))
```

### The sum of a nonpositive and a negative integer is negative

```agda
abstract
  is-negative-add-nonpositive-negative-ℤ :
    {x y : ℤ} → is-nonpositive-ℤ x → is-negative-ℤ y → is-negative-ℤ (x +ℤ y)
  is-negative-add-nonpositive-negative-ℤ {x} {y} H K =
    is-negative-eq-ℤ
      ( commutative-add-ℤ y x)
      ( is-negative-add-negative-nonnegative-ℤ K H)
```

### The sum of two nonpositive integers is nonpositive

```agda
abstract
  is-nonpositive-add-ℤ :
    {x y : ℤ} →
    is-nonpositive-ℤ x → is-nonpositive-ℤ y → is-nonpositive-ℤ (x +ℤ y)
  is-nonpositive-add-ℤ {x} {y} H K =
    is-nonpositive-eq-ℤ
      ( neg-neg-ℤ (x +ℤ y))
      ( is-nonpositive-neg-is-nonnegative-ℤ
        ( is-nonnegative-eq-ℤ
          ( inv (distributive-neg-add-ℤ x y))
          ( is-nonnegative-add-ℤ
            ( is-nonnegative-neg-is-nonpositive-ℤ H)
            ( is-nonnegative-neg-is-nonpositive-ℤ K))))
```

## Definitions

### Addition of positive integers

```agda
add-positive-ℤ : positive-ℤ → positive-ℤ → positive-ℤ
add-positive-ℤ (x , H) (y , K) = (add-ℤ x y , is-positive-add-ℤ H K)
```

### Addition of nonnegative integers

```agda
add-nonnegative-ℤ : nonnegative-ℤ → nonnegative-ℤ → nonnegative-ℤ
add-nonnegative-ℤ (x , H) (y , K) = (add-ℤ x y , is-nonnegative-add-ℤ H K)
```

### Addition of negative integers

```agda
add-negative-ℤ : negative-ℤ → negative-ℤ → negative-ℤ
add-negative-ℤ (x , H) (y , K) = (add-ℤ x y , is-negative-add-ℤ H K)
```

### Addition of nonpositive integers

```agda
add-nonpositive-ℤ : nonpositive-ℤ → nonpositive-ℤ → nonpositive-ℤ
add-nonpositive-ℤ (x , H) (y , K) = (add-ℤ x y , is-nonpositive-add-ℤ H K)
```
