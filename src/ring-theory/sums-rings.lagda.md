# Sums of elements in rings

```agda
module ring-theory.sums-rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels

open import linear-algebra.finite-sequences-on-rings

open import lists.finite-sequences

open import ring-theory.rings
open import ring-theory.sums-semirings

open import univalent-combinatorics.coproduct-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The sum operation extends the binary addition operation on a ring `R` to any
[finite sequence](lists.finite-sequences.md) of elements of `R`.

## Definition

```agda
sum-Ring :
  {l : Level} (R : Ring l) (n : ℕ) → fin-sequence-type-Ring R n → type-Ring R
sum-Ring R = sum-Semiring (semiring-Ring R)
```

## Properties

### Sums of one and two elements

```agda
module _
  {l : Level} (R : Ring l)
  where

  sum-one-element-Ring :
    (f : fin-sequence-type-Ring R 1) → sum-Ring R 1 f ＝ head-fin-sequence 0 f
  sum-one-element-Ring = sum-one-element-Semiring (semiring-Ring R)

  sum-two-elements-Ring :
    (f : fin-sequence-type-Ring R 2) →
    sum-Ring R 2 f ＝ add-Ring R (f (zero-Fin 1)) (f (one-Fin 1))
  sum-two-elements-Ring = sum-two-elements-Semiring (semiring-Ring R)
```

### Sums are homotopy invariant

```agda
module _
  {l : Level} (R : Ring l)
  where

  htpy-sum-Ring :
    (n : ℕ) {f g : fin-sequence-type-Ring R n} →
    (f ~ g) → sum-Ring R n f ＝ sum-Ring R n g
  htpy-sum-Ring = htpy-sum-Semiring (semiring-Ring R)
```

### Sums are equal to the zero-th term plus the rest

```agda
module _
  {l : Level} (R : Ring l)
  where

  cons-sum-Ring :
    (n : ℕ) (f : fin-sequence-type-Ring R (succ-ℕ n)) →
    {x : type-Ring R} → head-fin-sequence n f ＝ x →
    sum-Ring R (succ-ℕ n) f ＝
    add-Ring R (sum-Ring R n (tail-fin-sequence n f)) x
  cons-sum-Ring = cons-sum-Semiring (semiring-Ring R)

  snoc-sum-Ring :
    (n : ℕ) (f : fin-sequence-type-Ring R (succ-ℕ n)) →
    {x : type-Ring R} → f (zero-Fin n) ＝ x →
    sum-Ring R (succ-ℕ n) f ＝
    add-Ring R
      ( x)
      ( sum-Ring R n (f ∘ inr-Fin n))
  snoc-sum-Ring = snoc-sum-Semiring (semiring-Ring R)
```

### Multiplication distributes over sums

```agda
module _
  {l : Level} (R : Ring l)
  where

  left-distributive-mul-sum-Ring :
    (n : ℕ) (x : type-Ring R)
    (f : fin-sequence-type-Ring R n) →
    mul-Ring R x (sum-Ring R n f) ＝
    sum-Ring R n (λ i → mul-Ring R x (f i))
  left-distributive-mul-sum-Ring =
    left-distributive-mul-sum-Semiring (semiring-Ring R)

  right-distributive-mul-sum-Ring :
    (n : ℕ) (f : fin-sequence-type-Ring R n)
    (x : type-Ring R) →
    mul-Ring R (sum-Ring R n f) x ＝
    sum-Ring R n (λ i → mul-Ring R (f i) x)
  right-distributive-mul-sum-Ring =
    right-distributive-mul-sum-Semiring (semiring-Ring R)
```

### Interchange law of sums and addition in a semiring

```agda
module _
  {l : Level} (R : Ring l)
  where

  interchange-add-sum-Ring :
    (n : ℕ) (f g : fin-sequence-type-Ring R n) →
    add-Ring R
      ( sum-Ring R n f)
      ( sum-Ring R n g) ＝
    sum-Ring R n
      ( add-fin-sequence-type-Ring R n f g)
  interchange-add-sum-Ring = interchange-add-sum-Semiring (semiring-Ring R)
```

### Extending a sum of elements in a semiring

```agda
module _
  {l : Level} (R : Ring l)
  where

  extend-sum-Ring :
    (n : ℕ) (f : fin-sequence-type-Ring R n) →
    sum-Ring R
      ( succ-ℕ n)
      ( cons-fin-sequence-type-Ring R n (zero-Ring R) f) ＝
    sum-Ring R n f
  extend-sum-Ring = extend-sum-Semiring (semiring-Ring R)
```

### Shifting a sum of elements in a semiring

```agda
module _
  {l : Level} (R : Ring l)
  where

  shift-sum-Ring :
    (n : ℕ) (f : fin-sequence-type-Ring R n) →
    sum-Ring R
      ( succ-ℕ n)
      ( snoc-fin-sequence-type-Ring R n f
        ( zero-Ring R)) ＝
    sum-Ring R n f
  shift-sum-Ring = shift-sum-Semiring (semiring-Ring R)
```

### A sum of zeroes is zero

```agda
module _
  {l : Level} (R : Ring l)
  where

  sum-zero-Ring :
    (n : ℕ) → sum-Ring R n (zero-fin-sequence-type-Ring R n) ＝ zero-Ring R
  sum-zero-Ring = sum-zero-Semiring (semiring-Ring R)
```

### Splitting sums

```agda
split-sum-Ring :
  {l : Level} (R : Ring l)
  (n m : ℕ) (f : fin-sequence-type-Ring R (n +ℕ m)) →
  sum-Ring R (n +ℕ m) f ＝
  add-Ring R
    ( sum-Ring R n (f ∘ inl-coproduct-Fin n m))
    ( sum-Ring R m (f ∘ inr-coproduct-Fin n m))
split-sum-Ring R = split-sum-Semiring (semiring-Ring R)
```
