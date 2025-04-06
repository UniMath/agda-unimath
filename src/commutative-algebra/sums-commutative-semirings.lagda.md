# Sums in commutative semirings

```agda
module commutative-algebra.sums-commutative-semirings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-semirings

open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels

open import linear-algebra.tuples
open import linear-algebra.tuples-on-commutative-semirings

open import ring-theory.sums-semirings

open import univalent-combinatorics.coproduct-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The **sum operation** extends the binary addition operation on a commutative
semiring `R` to any family of elements of `R` indexed by a standard finite type.

## Definition

```agda
sum-Commutative-Semiring :
  {l : Level} (A : Commutative-Semiring l) (n : ℕ) →
  (functional-tuple-Commutative-Semiring A n) → type-Commutative-Semiring A
sum-Commutative-Semiring A = sum-Semiring (semiring-Commutative-Semiring A)
```

## Properties

### Sums of one and two elements

```agda
module _
  {l : Level} (A : Commutative-Semiring l)
  where

  sum-one-element-Commutative-Semiring :
    (f : functional-tuple-Commutative-Semiring A 1) →
    sum-Commutative-Semiring A 1 f ＝ head-functional-tuple 0 f
  sum-one-element-Commutative-Semiring =
    sum-one-element-Semiring (semiring-Commutative-Semiring A)

  sum-two-elements-Commutative-Semiring :
    (f : functional-tuple-Commutative-Semiring A 2) →
    sum-Commutative-Semiring A 2 f ＝
    add-Commutative-Semiring A (f (zero-Fin 1)) (f (one-Fin 1))
  sum-two-elements-Commutative-Semiring =
    sum-two-elements-Semiring (semiring-Commutative-Semiring A)
```

### Sums are homotopy invariant

```agda
module _
  {l : Level} (A : Commutative-Semiring l)
  where

  htpy-sum-Commutative-Semiring :
    (n : ℕ) {f g : functional-tuple-Commutative-Semiring A n} →
    (f ~ g) → sum-Commutative-Semiring A n f ＝ sum-Commutative-Semiring A n g
  htpy-sum-Commutative-Semiring =
    htpy-sum-Semiring (semiring-Commutative-Semiring A)
```

### Sums are equal to the zero-th term plus the rest

```agda
module _
  {l : Level} (A : Commutative-Semiring l)
  where

  cons-sum-Commutative-Semiring :
    (n : ℕ) (f : functional-tuple-Commutative-Semiring A (succ-ℕ n)) →
    {x : type-Commutative-Semiring A} → head-functional-tuple n f ＝ x →
    sum-Commutative-Semiring A (succ-ℕ n) f ＝
    add-Commutative-Semiring A
      ( sum-Commutative-Semiring A n (tail-functional-tuple n f)) x
  cons-sum-Commutative-Semiring =
    cons-sum-Semiring (semiring-Commutative-Semiring A)

  snoc-sum-Commutative-Semiring :
    (n : ℕ) (f : functional-tuple-Commutative-Semiring A (succ-ℕ n)) →
    {x : type-Commutative-Semiring A} → f (zero-Fin n) ＝ x →
    sum-Commutative-Semiring A (succ-ℕ n) f ＝
    add-Commutative-Semiring A
      ( x)
      ( sum-Commutative-Semiring A n (f ∘ inr-Fin n))
  snoc-sum-Commutative-Semiring =
    snoc-sum-Semiring (semiring-Commutative-Semiring A)
```

### Multiplication distributes over sums

```agda
module _
  {l : Level} (A : Commutative-Semiring l)
  where

  left-distributive-mul-sum-Commutative-Semiring :
    (n : ℕ) (x : type-Commutative-Semiring A)
    (f : functional-tuple-Commutative-Semiring A n) →
    mul-Commutative-Semiring A x (sum-Commutative-Semiring A n f) ＝
    sum-Commutative-Semiring A n (λ i → mul-Commutative-Semiring A x (f i))
  left-distributive-mul-sum-Commutative-Semiring =
    left-distributive-mul-sum-Semiring (semiring-Commutative-Semiring A)

  right-distributive-mul-sum-Commutative-Semiring :
    (n : ℕ) (f : functional-tuple-Commutative-Semiring A n)
    (x : type-Commutative-Semiring A) →
    mul-Commutative-Semiring A (sum-Commutative-Semiring A n f) x ＝
    sum-Commutative-Semiring A n (λ i → mul-Commutative-Semiring A (f i) x)
  right-distributive-mul-sum-Commutative-Semiring =
    right-distributive-mul-sum-Semiring (semiring-Commutative-Semiring A)
```

### Interchange law of sums and addition in a commutative semiring

```agda
module _
  {l : Level} (A : Commutative-Semiring l)
  where

  interchange-add-sum-Commutative-Semiring :
    (n : ℕ) (f g : functional-tuple-Commutative-Semiring A n) →
    add-Commutative-Semiring A
      ( sum-Commutative-Semiring A n f)
      ( sum-Commutative-Semiring A n g) ＝
    sum-Commutative-Semiring A n
      ( add-functional-tuple-Commutative-Semiring A n f g)
  interchange-add-sum-Commutative-Semiring =
    interchange-add-sum-Semiring (semiring-Commutative-Semiring A)
```

### Extending a sum of elements in a commutative semiring

```agda
module _
  {l : Level} (A : Commutative-Semiring l)
  where

  extend-sum-Commutative-Semiring :
    (n : ℕ) (f : functional-tuple-Commutative-Semiring A n) →
    sum-Commutative-Semiring A
      ( succ-ℕ n)
      ( cons-functional-tuple-Commutative-Semiring A n
        ( zero-Commutative-Semiring A) f) ＝
    sum-Commutative-Semiring A n f
  extend-sum-Commutative-Semiring =
    extend-sum-Semiring (semiring-Commutative-Semiring A)
```

### Shifting a sum of elements in a commutative semiring

```agda
module _
  {l : Level} (A : Commutative-Semiring l)
  where

  shift-sum-Commutative-Semiring :
    (n : ℕ) (f : functional-tuple-Commutative-Semiring A n) →
    sum-Commutative-Semiring A
      ( succ-ℕ n)
      ( snoc-functional-tuple-Commutative-Semiring A n f
        ( zero-Commutative-Semiring A)) ＝
    sum-Commutative-Semiring A n f
  shift-sum-Commutative-Semiring =
    shift-sum-Semiring (semiring-Commutative-Semiring A)
```

### A sum of zeroes is zero

```agda
module _
  {l : Level} (A : Commutative-Semiring l)
  where

  sum-zero-Commutative-Semiring :
    (n : ℕ) →
    sum-Commutative-Semiring A n
      ( zero-functional-tuple-Commutative-Semiring A n) ＝
    zero-Commutative-Semiring A
  sum-zero-Commutative-Semiring =
    sum-zero-Semiring (semiring-Commutative-Semiring A)
```

### Splitting sums

```agda
split-sum-Commutative-Semiring :
  {l : Level} (A : Commutative-Semiring l)
  (n m : ℕ) (f : functional-tuple-Commutative-Semiring A (n +ℕ m)) →
  sum-Commutative-Semiring A (n +ℕ m) f ＝
  add-Commutative-Semiring A
    ( sum-Commutative-Semiring A n (f ∘ inl-coproduct-Fin n m))
    ( sum-Commutative-Semiring A m (f ∘ inr-coproduct-Fin n m))
split-sum-Commutative-Semiring A =
  split-sum-Semiring (semiring-Commutative-Semiring A)
```
