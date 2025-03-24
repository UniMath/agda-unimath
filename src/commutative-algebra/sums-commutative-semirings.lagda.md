# Sums in commutative semirings

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module commutative-algebra.sums-commutative-semirings
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-semirings funext univalence truncations

open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.function-types funext
open import foundation.homotopies funext
open import foundation.identity-types funext
open import foundation.universe-levels

open import linear-algebra.vectors funext univalence truncations
open import linear-algebra.vectors-on-commutative-semirings funext univalence truncations

open import ring-theory.sums-semirings funext univalence truncations

open import univalent-combinatorics.coproduct-types funext univalence truncations
open import univalent-combinatorics.standard-finite-types funext univalence truncations
```

</details>

## Idea

The **sum operation** extends the binary addition operation on a commutative
semiring `R` to any family of elements of `R` indexed by a standard finite type.

## Definition

```agda
sum-Commutative-Semiring :
  {l : Level} (A : Commutative-Semiring l) (n : ℕ) →
  (functional-vec-Commutative-Semiring A n) → type-Commutative-Semiring A
sum-Commutative-Semiring A = sum-Semiring (semiring-Commutative-Semiring A)
```

## Properties

### Sums of one and two elements

```agda
module _
  {l : Level} (A : Commutative-Semiring l)
  where

  sum-one-element-Commutative-Semiring :
    (f : functional-vec-Commutative-Semiring A 1) →
    sum-Commutative-Semiring A 1 f ＝ head-functional-vec 0 f
  sum-one-element-Commutative-Semiring =
    sum-one-element-Semiring (semiring-Commutative-Semiring A)

  sum-two-elements-Commutative-Semiring :
    (f : functional-vec-Commutative-Semiring A 2) →
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
    (n : ℕ) {f g : functional-vec-Commutative-Semiring A n} →
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
    (n : ℕ) (f : functional-vec-Commutative-Semiring A (succ-ℕ n)) →
    {x : type-Commutative-Semiring A} → head-functional-vec n f ＝ x →
    sum-Commutative-Semiring A (succ-ℕ n) f ＝
    add-Commutative-Semiring A
      ( sum-Commutative-Semiring A n (tail-functional-vec n f)) x
  cons-sum-Commutative-Semiring =
    cons-sum-Semiring (semiring-Commutative-Semiring A)

  snoc-sum-Commutative-Semiring :
    (n : ℕ) (f : functional-vec-Commutative-Semiring A (succ-ℕ n)) →
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
    (f : functional-vec-Commutative-Semiring A n) →
    mul-Commutative-Semiring A x (sum-Commutative-Semiring A n f) ＝
    sum-Commutative-Semiring A n (λ i → mul-Commutative-Semiring A x (f i))
  left-distributive-mul-sum-Commutative-Semiring =
    left-distributive-mul-sum-Semiring (semiring-Commutative-Semiring A)

  right-distributive-mul-sum-Commutative-Semiring :
    (n : ℕ) (f : functional-vec-Commutative-Semiring A n)
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
    (n : ℕ) (f g : functional-vec-Commutative-Semiring A n) →
    add-Commutative-Semiring A
      ( sum-Commutative-Semiring A n f)
      ( sum-Commutative-Semiring A n g) ＝
    sum-Commutative-Semiring A n
      ( add-functional-vec-Commutative-Semiring A n f g)
  interchange-add-sum-Commutative-Semiring =
    interchange-add-sum-Semiring (semiring-Commutative-Semiring A)
```

### Extending a sum of elements in a commutative semiring

```agda
module _
  {l : Level} (A : Commutative-Semiring l)
  where

  extend-sum-Commutative-Semiring :
    (n : ℕ) (f : functional-vec-Commutative-Semiring A n) →
    sum-Commutative-Semiring A
      ( succ-ℕ n)
      ( cons-functional-vec-Commutative-Semiring A n
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
    (n : ℕ) (f : functional-vec-Commutative-Semiring A n) →
    sum-Commutative-Semiring A
      ( succ-ℕ n)
      ( snoc-functional-vec-Commutative-Semiring A n f
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
      ( zero-functional-vec-Commutative-Semiring A n) ＝
    zero-Commutative-Semiring A
  sum-zero-Commutative-Semiring =
    sum-zero-Semiring (semiring-Commutative-Semiring A)
```

### Splitting sums

```agda
split-sum-Commutative-Semiring :
  {l : Level} (A : Commutative-Semiring l)
  (n m : ℕ) (f : functional-vec-Commutative-Semiring A (n +ℕ m)) →
  sum-Commutative-Semiring A (n +ℕ m) f ＝
  add-Commutative-Semiring A
    ( sum-Commutative-Semiring A n (f ∘ inl-coproduct-Fin n m))
    ( sum-Commutative-Semiring A m (f ∘ inr-coproduct-Fin n m))
split-sum-Commutative-Semiring A =
  split-sum-Semiring (semiring-Commutative-Semiring A)
```
