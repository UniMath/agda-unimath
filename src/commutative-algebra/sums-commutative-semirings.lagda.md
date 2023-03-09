# Sums in commutative semirings

```agda
module commutative-algebra.sums-commutative-semirings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-semirings

open import elementary-number-theory.natural-numbers

open import foundation.coproduct-types
open import foundation.functions
open import foundation.homotopies
open import foundation.identity-types
open import foundation.unit-type
open import foundation.universe-levels

open import linear-algebra.vectors
open import linear-algebra.vectors-on-commutative-semirings

open import ring-theory.sums-semirings

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The sum operation extends the binary addition operation on a commutative semiring `R` to any family of elements of `R` indexed by a standard finite type.

## Definition

```agda
sum-Commutative-Semiring :
  {l : Level} (R : Commutative-Semiring l) (n : ℕ) →
  (functional-vec-Commutative-Semiring R n) → type-Commutative-Semiring R
sum-Commutative-Semiring R = sum-Semiring (semiring-Commutative-Semiring R)
```

## Properties

### Sums of one and two elements

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  sum-one-element-Commutative-Semiring :
    (f : functional-vec-Commutative-Semiring R 1) →
    sum-Commutative-Semiring R 1 f ＝ head-functional-vec 0 f
  sum-one-element-Commutative-Semiring =
    sum-one-element-Semiring (semiring-Commutative-Semiring R)

  sum-two-elements-Commutative-Semiring :
    (f : functional-vec-Commutative-Semiring R 2) →
    sum-Commutative-Semiring R 2 f ＝
    add-Commutative-Semiring R (f (zero-Fin 1)) (f (one-Fin 1))
  sum-two-elements-Commutative-Semiring =
    sum-two-elements-Semiring (semiring-Commutative-Semiring R)
```

### Sums are homotopy invariant

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  htpy-sum-Commutative-Semiring :
    (n : ℕ) {f g : functional-vec-Commutative-Semiring R n} →
    (f ~ g) → sum-Commutative-Semiring R n f ＝ sum-Commutative-Semiring R n g
  htpy-sum-Commutative-Semiring =
    htpy-sum-Semiring (semiring-Commutative-Semiring R)
```

### Sums are equal to the zero-th term plus the rest

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  cons-sum-Commutative-Semiring :
    (n : ℕ) (f : functional-vec-Commutative-Semiring R (succ-ℕ n)) →
    {x : type-Commutative-Semiring R} → head-functional-vec n f ＝ x →
    sum-Commutative-Semiring R (succ-ℕ n) f ＝
    add-Commutative-Semiring R
      ( sum-Commutative-Semiring R n (tail-functional-vec n f)) x
  cons-sum-Commutative-Semiring =
    cons-sum-Semiring (semiring-Commutative-Semiring R)

  snoc-sum-Commutative-Semiring :
    (n : ℕ) (f : functional-vec-Commutative-Semiring R (succ-ℕ n)) →
    {x : type-Commutative-Semiring R} → f (zero-Fin n) ＝ x →
    sum-Commutative-Semiring R (succ-ℕ n) f ＝
    add-Commutative-Semiring R
      ( x)
      ( sum-Commutative-Semiring R n (f ∘ inr-Fin n))
  snoc-sum-Commutative-Semiring =
    snoc-sum-Semiring (semiring-Commutative-Semiring R)
```

### Multiplication distributes over sums

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  left-distributive-mul-sum-Commutative-Semiring :
    (n : ℕ) (x : type-Commutative-Semiring R)
    (f : functional-vec-Commutative-Semiring R n) →
    mul-Commutative-Semiring R x (sum-Commutative-Semiring R n f) ＝
    sum-Commutative-Semiring R n (λ i → mul-Commutative-Semiring R x (f i))
  left-distributive-mul-sum-Commutative-Semiring =
    left-distributive-mul-sum-Semiring (semiring-Commutative-Semiring R)

  right-distributive-mul-sum-Commutative-Semiring :
    (n : ℕ) (f : functional-vec-Commutative-Semiring R n)
    (x : type-Commutative-Semiring R) →
    mul-Commutative-Semiring R (sum-Commutative-Semiring R n f) x ＝
    sum-Commutative-Semiring R n (λ i → mul-Commutative-Semiring R (f i) x)
  right-distributive-mul-sum-Commutative-Semiring =
    right-distributive-mul-sum-Semiring (semiring-Commutative-Semiring R)
```

### Interchange law of sums and addition in a commutative ring

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  interchange-add-sum-Commutative-Semiring :
    (n : ℕ) (f g : functional-vec-Commutative-Semiring R n) →
    add-Commutative-Semiring R
      ( sum-Commutative-Semiring R n f)
      ( sum-Commutative-Semiring R n g) ＝
    sum-Commutative-Semiring R n
      ( add-functional-vec-Commutative-Semiring R n f g)
  interchange-add-sum-Commutative-Semiring =
    interchange-add-sum-Semiring (semiring-Commutative-Semiring R)
```

### Extending a sum of elements in a commutative ring

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  extend-sum-Commutative-Semiring :
    (n : ℕ) (f : functional-vec-Commutative-Semiring R n) →
    sum-Commutative-Semiring R
      ( succ-ℕ n)
      ( cons-functional-vec-Commutative-Semiring R n
        ( zero-Commutative-Semiring R) f) ＝
    sum-Commutative-Semiring R n f
  extend-sum-Commutative-Semiring =
    extend-sum-Semiring (semiring-Commutative-Semiring R)
```

### Shifting a sum of elements in a commutative ring

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  shift-sum-Commutative-Semiring :
    (n : ℕ) (f : functional-vec-Commutative-Semiring R n) →
    sum-Commutative-Semiring R
      ( succ-ℕ n)
      ( snoc-functional-vec-Commutative-Semiring R n f
        ( zero-Commutative-Semiring R)) ＝
    sum-Commutative-Semiring R n f
  shift-sum-Commutative-Semiring =
    shift-sum-Semiring (semiring-Commutative-Semiring R)
```
