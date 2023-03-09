# Sums in commutative rings

```agda
module commutative-algebra.sums-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import elementary-number-theory.natural-numbers

open import foundation.coproduct-types
open import foundation.functions
open import foundation.homotopies
open import foundation.identity-types
open import foundation.unit-type
open import foundation.universe-levels

open import linear-algebra.vectors
open import linear-algebra.vectors-on-commutative-rings

open import ring-theory.sums-rings

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The sum operation extends the binary addition operation on a commutative ring `R` to any family of elements of `R` indexed by a standard finite type.

## Definition

```agda
sum-Commutative-Ring :
  {l : Level} (R : Commutative-Ring l) (n : ℕ) →
  (functional-vec-Commutative-Ring R n) → type-Commutative-Ring R
sum-Commutative-Ring R = sum-Ring (ring-Commutative-Ring R)
```

## Properties

### Sums of one and two elements

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  sum-one-element-Commutative-Ring :
    (f : functional-vec-Commutative-Ring R 1) →
    sum-Commutative-Ring R 1 f ＝ head-functional-vec 0 f
  sum-one-element-Commutative-Ring =
    sum-one-element-Ring (ring-Commutative-Ring R)

  sum-two-elements-Commutative-Ring :
    (f : functional-vec-Commutative-Ring R 2) →
    sum-Commutative-Ring R 2 f ＝
    add-Commutative-Ring R (f (zero-Fin 1)) (f (one-Fin 1))
  sum-two-elements-Commutative-Ring =
    sum-two-elements-Ring (ring-Commutative-Ring R)
```

### Sums are homotopy invariant

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  htpy-sum-Commutative-Ring :
    (n : ℕ) {f g : functional-vec-Commutative-Ring R n} →
    (f ~ g) → sum-Commutative-Ring R n f ＝ sum-Commutative-Ring R n g
  htpy-sum-Commutative-Ring = htpy-sum-Ring (ring-Commutative-Ring R)
```

### Sums are equal to the zero-th term plus the rest

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  cons-sum-Commutative-Ring :
    (n : ℕ) (f : functional-vec-Commutative-Ring R (succ-ℕ n)) →
    {x : type-Commutative-Ring R} → head-functional-vec n f ＝ x →
    sum-Commutative-Ring R (succ-ℕ n) f ＝
    add-Commutative-Ring R
      ( sum-Commutative-Ring R n (tail-functional-vec n f)) x
  cons-sum-Commutative-Ring = cons-sum-Ring (ring-Commutative-Ring R)

  snoc-sum-Commutative-Ring :
    (n : ℕ) (f : functional-vec-Commutative-Ring R (succ-ℕ n)) →
    {x : type-Commutative-Ring R} → f (zero-Fin n) ＝ x →
    sum-Commutative-Ring R (succ-ℕ n) f ＝
    add-Commutative-Ring R
      ( x)
      ( sum-Commutative-Ring R n (f ∘ inr-Fin n))
  snoc-sum-Commutative-Ring = snoc-sum-Ring (ring-Commutative-Ring R)
```

### Multiplication distributes over sums

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  left-distributive-mul-sum-Commutative-Ring :
    (n : ℕ) (x : type-Commutative-Ring R)
    (f : functional-vec-Commutative-Ring R n) →
    mul-Commutative-Ring R x (sum-Commutative-Ring R n f) ＝
    sum-Commutative-Ring R n (λ i → mul-Commutative-Ring R x (f i))
  left-distributive-mul-sum-Commutative-Ring =
    left-distributive-mul-sum-Ring (ring-Commutative-Ring R)

  right-distributive-mul-sum-Commutative-Ring :
    (n : ℕ) (f : functional-vec-Commutative-Ring R n)
    (x : type-Commutative-Ring R) →
    mul-Commutative-Ring R (sum-Commutative-Ring R n f) x ＝
    sum-Commutative-Ring R n (λ i → mul-Commutative-Ring R (f i) x)
  right-distributive-mul-sum-Commutative-Ring =
    right-distributive-mul-sum-Ring (ring-Commutative-Ring R)
```

### Interchange law of sums and addition in a commutative ring

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  interchange-add-sum-Commutative-Ring :
    (n : ℕ) (f g : functional-vec-Commutative-Ring R n) →
    add-Commutative-Ring R
      ( sum-Commutative-Ring R n f)
      ( sum-Commutative-Ring R n g) ＝
    sum-Commutative-Ring R n
      ( add-functional-vec-Commutative-Ring R n f g)
  interchange-add-sum-Commutative-Ring =
    interchange-add-sum-Ring (ring-Commutative-Ring R)
```

### Extending a sum of elements in a commutative ring

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  extend-sum-Commutative-Ring :
    (n : ℕ) (f : functional-vec-Commutative-Ring R n) →
    sum-Commutative-Ring R
      ( succ-ℕ n)
      ( cons-functional-vec-Commutative-Ring R n (zero-Commutative-Ring R) f) ＝
    sum-Commutative-Ring R n f
  extend-sum-Commutative-Ring = extend-sum-Ring (ring-Commutative-Ring R)
```

### Shifting a sum of elements in a commutative ring

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  shift-sum-Commutative-Ring :
    (n : ℕ) (f : functional-vec-Commutative-Ring R n) →
    sum-Commutative-Ring R
      ( succ-ℕ n)
      ( snoc-functional-vec-Commutative-Ring R n f
        ( zero-Commutative-Ring R)) ＝
    sum-Commutative-Ring R n f
  shift-sum-Commutative-Ring = shift-sum-Ring (ring-Commutative-Ring R)
```
