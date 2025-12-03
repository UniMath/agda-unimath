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
open import elementary-number-theory.nonzero-natural-numbers
open import elementary-number-theory.positive-and-negative-integers
open import elementary-number-theory.positive-integers
open import elementary-number-theory.strict-inequality-integers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.transport-along-identifications
open import foundation.unit-type
```

</details>

## Idea

When we have information about the sign of the factors of an
[integer product](elementary-number-theory.multiplication-integers.md), we can
deduce the sign of their product too. The table below tabulates every case and
displays the corresponding Agda definition.

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
strict inequality and multiplication by a nonpositive integer preserves
inequality.

## Lemmas

### The product of two positive integers is positive

```agda
is-positive-mul-ℤ :
  {x y : ℤ} → is-positive-ℤ x → is-positive-ℤ y → is-positive-ℤ (x *ℤ y)
is-positive-mul-ℤ {inr (inr zero-ℕ)} {y} H K = K
is-positive-mul-ℤ {inr (inr (succ-ℕ x))} {y} H K =
  is-positive-add-ℤ K (is-positive-mul-ℤ {inr (inr x)} H K)
```

### The product of a positive and a nonnegative integer is nonnegative

```agda
is-nonnegative-mul-positive-nonnegative-ℤ :
  {x y : ℤ} → is-positive-ℤ x → is-nonnegative-ℤ y → is-nonnegative-ℤ (x *ℤ y)
is-nonnegative-mul-positive-nonnegative-ℤ {inr (inr zero-ℕ)} {y} H K = K
is-nonnegative-mul-positive-nonnegative-ℤ {inr (inr (succ-ℕ x))} {y} H K =
  is-nonnegative-add-ℤ K
    ( is-nonnegative-mul-positive-nonnegative-ℤ {inr (inr x)} H K)
```

### The product of a positive and a negative integer is negative

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

### The product of a positive and a nonpositive integer is nonpositive

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

### The product of a nonnegative integer and a positive integer is nonnegative

```agda
is-nonnegative-mul-nonnegative-positive-ℤ :
  {x y : ℤ} → is-nonnegative-ℤ x → is-positive-ℤ y → is-nonnegative-ℤ (x *ℤ y)
is-nonnegative-mul-nonnegative-positive-ℤ {x} {y} H K =
  is-nonnegative-eq-ℤ
    ( commutative-mul-ℤ y x)
    ( is-nonnegative-mul-positive-nonnegative-ℤ K H)
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

### The product of a nonnegative and a negative integer is nonpositive

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

### The product of a nonnegative and a nonpositive integer is nonpositive

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

### The product of a negative and a positive integer is negative

```agda
is-negative-mul-negative-positive-ℤ :
  {x y : ℤ} → is-negative-ℤ x → is-positive-ℤ y → is-negative-ℤ (x *ℤ y)
is-negative-mul-negative-positive-ℤ {x} {y} H K =
  is-negative-eq-ℤ
    ( commutative-mul-ℤ y x)
    ( is-negative-mul-positive-negative-ℤ K H)
```

### The product of a negative and a nonnegative integer is nonpositive

```agda
is-nonpositive-mul-negative-nonnegative-ℤ :
  {x y : ℤ} → is-negative-ℤ x → is-nonnegative-ℤ y → is-nonpositive-ℤ (x *ℤ y)
is-nonpositive-mul-negative-nonnegative-ℤ {x} {y} H K =
  is-nonpositive-eq-ℤ
    ( commutative-mul-ℤ y x)
    ( is-nonpositive-mul-nonnegative-negative-ℤ K H)
```

### The product of two negative integers is positive

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

### The product of a negative and a nonpositive integer is nonnegative

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

### The product of a nonpositive and a positive integer is nonpositive

```agda
is-nonpositive-mul-nonpositive-positive-ℤ :
  {x y : ℤ} → is-nonpositive-ℤ x → is-positive-ℤ y → is-nonpositive-ℤ (x *ℤ y)
is-nonpositive-mul-nonpositive-positive-ℤ {x} {y} H K =
  is-nonpositive-eq-ℤ
    ( commutative-mul-ℤ y x)
    ( is-nonpositive-mul-positive-nonpositive-ℤ K H)
```

### The product of a nonpositive and a nonnegative integer is nonpositive

```agda
is-nonpositive-mul-nonpositive-nonnegative-ℤ :
  {x y : ℤ} →
  is-nonpositive-ℤ x → is-nonnegative-ℤ y → is-nonpositive-ℤ (x *ℤ y)
is-nonpositive-mul-nonpositive-nonnegative-ℤ {x} {y} H K =
  is-nonpositive-eq-ℤ
    ( commutative-mul-ℤ y x)
    ( is-nonpositive-mul-nonnegative-nonpositive-ℤ K H)
```

### The product of a nonpositive integer and a negative integer is nonnegative

```agda
is-nonnegative-mul-nonpositive-negative-ℤ :
  { x y : ℤ} → is-nonpositive-ℤ x → is-negative-ℤ y → is-nonnegative-ℤ (x *ℤ y)
is-nonnegative-mul-nonpositive-negative-ℤ {x} {y} H K =
  is-nonnegative-eq-ℤ
    ( commutative-mul-ℤ y x)
    ( is-nonnegative-mul-negative-nonpositive-ℤ K H)
```

### The product of two nonpositive integers is nonnegative

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

### The left factor of a nonnegative product with a positive right factor is nonnegative

```agda
is-nonnegative-left-factor-mul-ℤ :
  {x y : ℤ} → is-nonnegative-ℤ (x *ℤ y) → is-positive-ℤ y → is-nonnegative-ℤ x
is-nonnegative-left-factor-mul-ℤ {inl x} {inr (inr y)} H K =
  ex-falso (is-nonnegative-eq-ℤ (compute-mul-ℤ (inl x) (inr (inr y))) H)
is-nonnegative-left-factor-mul-ℤ {inr x} {inr y} H K = star
```

### The right factor of a nonnegative product with a positive left factor is nonnegative

```agda
is-nonnegative-right-factor-mul-ℤ :
  {x y : ℤ} → is-nonnegative-ℤ (x *ℤ y) → is-positive-ℤ x → is-nonnegative-ℤ y
is-nonnegative-right-factor-mul-ℤ {x} {y} H =
  is-nonnegative-left-factor-mul-ℤ
    ( is-nonnegative-eq-ℤ (commutative-mul-ℤ x y) H)
```

### The left factor of a negative product with a positive right factor is negative

```agda
abstract
  is-negative-left-factor-mul-positive-ℤ :
    {x y : ℤ} → is-negative-ℤ (x *ℤ y) → is-positive-ℤ y → is-negative-ℤ x
  is-negative-left-factor-mul-positive-ℤ {inl x} {inr (inr y)} _ _ = star
  is-negative-left-factor-mul-positive-ℤ {inr x} {inr (inr y)} H _ =
    is-not-negative-and-nonnegative-ℤ
      ( inr x *ℤ inr (inr y))
      ( H ,
        is-nonnegative-mul-nonnegative-positive-ℤ
          { inr x}
          { inr (inr y)}
          ( star)
          ( star))
```

### The right factor of a negative product with a positive right factor is negative

```agda
abstract
  is-negative-right-factor-mul-positive-ℤ :
    {x y : ℤ} → is-negative-ℤ (x *ℤ y) → is-positive-ℤ x → is-negative-ℤ y
  is-negative-right-factor-mul-positive-ℤ {x} {y} xy-is-neg =
    is-negative-left-factor-mul-positive-ℤ
      ( tr is-negative-ℤ (commutative-mul-ℤ x y) xy-is-neg)
```

## Definitions

### Multiplication by a signed integer

```agda
int-mul-positive-ℤ : positive-ℤ → ℤ → ℤ
int-mul-positive-ℤ x y = int-positive-ℤ x *ℤ y

int-mul-positive-ℤ' : positive-ℤ → ℤ → ℤ
int-mul-positive-ℤ' x y = y *ℤ int-positive-ℤ x

int-mul-nonnegative-ℤ : nonnegative-ℤ → ℤ → ℤ
int-mul-nonnegative-ℤ x y = int-nonnegative-ℤ x *ℤ y

int-mul-nonnegative-ℤ' : nonnegative-ℤ → ℤ → ℤ
int-mul-nonnegative-ℤ' x y = y *ℤ int-nonnegative-ℤ x

int-mul-negative-ℤ : negative-ℤ → ℤ → ℤ
int-mul-negative-ℤ x y = int-negative-ℤ x *ℤ y

int-mul-negative-ℤ' : negative-ℤ → ℤ → ℤ
int-mul-negative-ℤ' x y = y *ℤ int-negative-ℤ x

int-mul-nonpositive-ℤ : nonpositive-ℤ → ℤ → ℤ
int-mul-nonpositive-ℤ x y = int-nonpositive-ℤ x *ℤ y

int-mul-nonpositive-ℤ' : nonpositive-ℤ → ℤ → ℤ
int-mul-nonpositive-ℤ' x y = y *ℤ int-nonpositive-ℤ x
```

### Multiplication of positive integers

```agda
mul-positive-ℤ : positive-ℤ → positive-ℤ → positive-ℤ
mul-positive-ℤ (x , H) (y , K) = (mul-ℤ x y , is-positive-mul-ℤ H K)

infixl 40 _*ℤ⁺_
_*ℤ⁺_ : ℤ⁺ → ℤ⁺ → ℤ⁺
_*ℤ⁺_ = mul-positive-ℤ
```

### Multiplication of nonnegative integers

```agda
mul-nonnegative-ℤ : nonnegative-ℤ → nonnegative-ℤ → nonnegative-ℤ
mul-nonnegative-ℤ (x , H) (y , K) = (mul-ℤ x y , is-nonnegative-mul-ℤ H K)
```

### Multiplication of negative integers

```agda
mul-negative-ℤ : negative-ℤ → negative-ℤ → positive-ℤ
mul-negative-ℤ (x , H) (y , K) = (mul-ℤ x y , is-positive-mul-negative-ℤ H K)
```

### Multiplication of nonpositive integers

```agda
mul-nonpositive-ℤ : nonpositive-ℤ → nonpositive-ℤ → nonnegative-ℤ
mul-nonpositive-ℤ (x , H) (y , K) =
  (mul-ℤ x y , is-nonnegative-mul-nonpositive-ℤ H K)
```

## Properties

### Multiplication by a positive integer preserves and reflects the strict ordering

```agda
module _
  (z : positive-ℤ) (x y : ℤ)
  where

  preserves-le-right-mul-positive-ℤ :
    le-ℤ x y → le-ℤ (int-mul-positive-ℤ z x) (int-mul-positive-ℤ z y)
  preserves-le-right-mul-positive-ℤ K =
    is-positive-eq-ℤ
      ( left-distributive-mul-diff-ℤ (int-positive-ℤ z) y x)
      ( is-positive-mul-ℤ (is-positive-int-positive-ℤ z) K)

  preserves-le-left-mul-positive-ℤ :
    le-ℤ x y → le-ℤ (int-mul-positive-ℤ' z x) (int-mul-positive-ℤ' z y)
  preserves-le-left-mul-positive-ℤ K =
    is-positive-eq-ℤ
      ( right-distributive-mul-diff-ℤ y x (int-positive-ℤ z))
      ( is-positive-mul-ℤ K (is-positive-int-positive-ℤ z))

  reflects-le-right-mul-positive-ℤ :
    le-ℤ (int-mul-positive-ℤ z x) (int-mul-positive-ℤ z y) → le-ℤ x y
  reflects-le-right-mul-positive-ℤ K =
    is-positive-right-factor-mul-ℤ
      ( is-positive-eq-ℤ
        ( inv (left-distributive-mul-diff-ℤ (int-positive-ℤ z) y x))
        ( K))
      ( is-positive-int-positive-ℤ z)

  reflects-le-left-mul-positive-ℤ :
    le-ℤ (int-mul-positive-ℤ' z x) (int-mul-positive-ℤ' z y) → le-ℤ x y
  reflects-le-left-mul-positive-ℤ K =
    is-positive-left-factor-mul-ℤ
      ( is-positive-eq-ℤ
      ( inv (right-distributive-mul-diff-ℤ y x (int-positive-ℤ z)))
        ( K))
      ( is-positive-int-positive-ℤ z)
```

### Multiplication by a nonnegative integer preserves inequality

```agda
module _
  (z : nonnegative-ℤ) (x y : ℤ)
  where

  preserves-leq-right-mul-nonnegative-ℤ :
    leq-ℤ x y → leq-ℤ (int-mul-nonnegative-ℤ z x) (int-mul-nonnegative-ℤ z y)
  preserves-leq-right-mul-nonnegative-ℤ K =
    is-nonnegative-eq-ℤ
      ( left-distributive-mul-diff-ℤ (int-nonnegative-ℤ z) y x)
      ( is-nonnegative-mul-ℤ (is-nonnegative-int-nonnegative-ℤ z) K)

  preserves-leq-left-mul-nonnegative-ℤ :
    leq-ℤ x y → leq-ℤ (int-mul-nonnegative-ℤ' z x) (int-mul-nonnegative-ℤ' z y)
  preserves-leq-left-mul-nonnegative-ℤ K =
    is-nonnegative-eq-ℤ
      ( right-distributive-mul-diff-ℤ y x (int-nonnegative-ℤ z))
      ( is-nonnegative-mul-ℤ K (is-nonnegative-int-nonnegative-ℤ z))
```

### The canonical embedding of positive integers in the nonzero natural numbers preserves multiplication

```agda
abstract
  mul-positive-nat-ℤ⁺ :
    (k l : ℤ⁺) →
    positive-nat-ℤ⁺ k *ℕ⁺ positive-nat-ℤ⁺ l ＝ positive-nat-ℤ⁺ (k *ℤ⁺ l)
  mul-positive-nat-ℤ⁺ k⁺@(k , _) l⁺@(l , _) =
    inv
      ( is-injective-is-equiv
        ( is-equiv-positive-int-ℕ⁺)
        ( ( is-section-positive-nat-ℤ⁺ _) ∙
          ( eq-ℤ⁺
            ( k⁺ *ℤ⁺ l⁺)
            ( positive-int-ℕ⁺ (positive-nat-ℤ⁺ k⁺ *ℕ⁺ positive-nat-ℤ⁺ l⁺))
            ( equational-reasoning
              k *ℤ l
              ＝
                int-ℕ (nat-ℕ⁺ (positive-nat-ℤ⁺ k⁺)) *ℤ
                int-ℕ (nat-ℕ⁺ (positive-nat-ℤ⁺ l⁺))
                by
                  ap-mul-ℤ
                    ( inv (ap int-ℤ⁺ (is-section-positive-nat-ℤ⁺ k⁺)))
                    ( inv (ap int-ℤ⁺ (is-section-positive-nat-ℤ⁺ l⁺)))
              ＝
                int-ℕ (nat-ℕ⁺ (positive-nat-ℤ⁺ k⁺ *ℕ⁺ positive-nat-ℤ⁺ l⁺))
                by
                  mul-int-ℕ
                    ( nat-ℕ⁺ (positive-nat-ℤ⁺ k⁺))
                    ( nat-ℕ⁺ (positive-nat-ℤ⁺ l⁺))))))
```

### Multiplication of positive integers is commutative

```agda
abstract
  commutative-mul-ℤ⁺ : (k l : ℤ⁺) → k *ℤ⁺ l ＝ l *ℤ⁺ k
  commutative-mul-ℤ⁺ (k , _) (l , _) = eq-ℤ⁺ _ _ (commutative-mul-ℤ k l)
```
