# Sums in commutative rings

```agda
module commutative-algebra.sums-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.unit-type
open import foundation.universe-levels

open import linear-algebra.finite-sequences-in-commutative-rings

open import lists.finite-sequences

open import ring-theory.sums-rings

open import univalent-combinatorics.coproduct-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The **sum operation** extends the binary addition operation on a commutative
ring `A` to any [finite sequence](lists.finite-sequences.md) of elements of `A`.

## Definition

```agda
sum-Commutative-Ring :
  {l : Level} (A : Commutative-Ring l) (n : ℕ) →
  (fin-sequence-type-Commutative-Ring A n) → type-Commutative-Ring A
sum-Commutative-Ring A = sum-Ring (ring-Commutative-Ring A)
```

## Properties

### Sums of one and two elements

```agda
module _
  {l : Level} (A : Commutative-Ring l)
  where

  sum-one-element-Commutative-Ring :
    (f : fin-sequence-type-Commutative-Ring A 1) →
    sum-Commutative-Ring A 1 f ＝ head-fin-sequence 0 f
  sum-one-element-Commutative-Ring =
    sum-one-element-Ring (ring-Commutative-Ring A)

  sum-two-elements-Commutative-Ring :
    (f : fin-sequence-type-Commutative-Ring A 2) →
    sum-Commutative-Ring A 2 f ＝
    add-Commutative-Ring A (f (zero-Fin 1)) (f (one-Fin 1))
  sum-two-elements-Commutative-Ring =
    sum-two-elements-Ring (ring-Commutative-Ring A)
```

### Sums are homotopy invariant

```agda
module _
  {l : Level} (A : Commutative-Ring l)
  where

  htpy-sum-Commutative-Ring :
    (n : ℕ) {f g : fin-sequence-type-Commutative-Ring A n} →
    (f ~ g) → sum-Commutative-Ring A n f ＝ sum-Commutative-Ring A n g
  htpy-sum-Commutative-Ring = htpy-sum-Ring (ring-Commutative-Ring A)
```

### Sums are equal to the zero-th term plus the rest

```agda
module _
  {l : Level} (A : Commutative-Ring l)
  where

  cons-sum-Commutative-Ring :
    (n : ℕ) (f : fin-sequence-type-Commutative-Ring A (succ-ℕ n)) →
    {x : type-Commutative-Ring A} → head-fin-sequence n f ＝ x →
    sum-Commutative-Ring A (succ-ℕ n) f ＝
    add-Commutative-Ring A
      ( sum-Commutative-Ring A n (tail-fin-sequence n f)) x
  cons-sum-Commutative-Ring = cons-sum-Ring (ring-Commutative-Ring A)

  snoc-sum-Commutative-Ring :
    (n : ℕ) (f : fin-sequence-type-Commutative-Ring A (succ-ℕ n)) →
    {x : type-Commutative-Ring A} → f (zero-Fin n) ＝ x →
    sum-Commutative-Ring A (succ-ℕ n) f ＝
    add-Commutative-Ring A
      ( x)
      ( sum-Commutative-Ring A n (f ∘ inr-Fin n))
  snoc-sum-Commutative-Ring = snoc-sum-Ring (ring-Commutative-Ring A)
```

### Multiplication distributes over sums

```agda
module _
  {l : Level} (A : Commutative-Ring l)
  where

  left-distributive-mul-sum-Commutative-Ring :
    (n : ℕ) (x : type-Commutative-Ring A)
    (f : fin-sequence-type-Commutative-Ring A n) →
    mul-Commutative-Ring A x (sum-Commutative-Ring A n f) ＝
    sum-Commutative-Ring A n (λ i → mul-Commutative-Ring A x (f i))
  left-distributive-mul-sum-Commutative-Ring =
    left-distributive-mul-sum-Ring (ring-Commutative-Ring A)

  right-distributive-mul-sum-Commutative-Ring :
    (n : ℕ) (f : fin-sequence-type-Commutative-Ring A n)
    (x : type-Commutative-Ring A) →
    mul-Commutative-Ring A (sum-Commutative-Ring A n f) x ＝
    sum-Commutative-Ring A n (λ i → mul-Commutative-Ring A (f i) x)
  right-distributive-mul-sum-Commutative-Ring =
    right-distributive-mul-sum-Ring (ring-Commutative-Ring A)
```

### Interchange law of sums and addition in a commutative ring

```agda
module _
  {l : Level} (A : Commutative-Ring l)
  where

  interchange-add-sum-Commutative-Ring :
    (n : ℕ) (f g : fin-sequence-type-Commutative-Ring A n) →
    add-Commutative-Ring A
      ( sum-Commutative-Ring A n f)
      ( sum-Commutative-Ring A n g) ＝
    sum-Commutative-Ring A n
      ( add-fin-sequence-type-Commutative-Ring A n f g)
  interchange-add-sum-Commutative-Ring =
    interchange-add-sum-Ring (ring-Commutative-Ring A)
```

### Extending a sum of elements in a commutative ring

```agda
module _
  {l : Level} (A : Commutative-Ring l)
  where

  extend-sum-Commutative-Ring :
    (n : ℕ) (f : fin-sequence-type-Commutative-Ring A n) →
    sum-Commutative-Ring A
      ( succ-ℕ n)
      ( cons-fin-sequence-type-Commutative-Ring
        ( A)
        ( n)
        ( zero-Commutative-Ring A)
        ( f)) ＝
    sum-Commutative-Ring A n f
  extend-sum-Commutative-Ring = extend-sum-Ring (ring-Commutative-Ring A)
```

### Shifting a sum of elements in a commutative ring

```agda
module _
  {l : Level} (A : Commutative-Ring l)
  where

  shift-sum-Commutative-Ring :
    (n : ℕ) (f : fin-sequence-type-Commutative-Ring A n) →
    sum-Commutative-Ring A
      ( succ-ℕ n)
      ( snoc-fin-sequence-type-Commutative-Ring A n f
        ( zero-Commutative-Ring A)) ＝
    sum-Commutative-Ring A n f
  shift-sum-Commutative-Ring = shift-sum-Ring (ring-Commutative-Ring A)
```

### Splitting sums

```agda
split-sum-Commutative-Ring :
  {l : Level} (A : Commutative-Ring l)
  (n m : ℕ) (f : fin-sequence-type-Commutative-Ring A (n +ℕ m)) →
  sum-Commutative-Ring A (n +ℕ m) f ＝
  add-Commutative-Ring A
    ( sum-Commutative-Ring A n (f ∘ inl-coproduct-Fin n m))
    ( sum-Commutative-Ring A m (f ∘ inr-coproduct-Fin n m))
split-sum-Commutative-Ring A n zero-ℕ f =
  inv (right-unit-law-add-Commutative-Ring A (sum-Commutative-Ring A n f))
split-sum-Commutative-Ring A n (succ-ℕ m) f =
  ( ap
    ( add-Commutative-Ring' A (f (inr star)))
    ( split-sum-Commutative-Ring A n m (f ∘ inl))) ∙
  ( associative-add-Commutative-Ring A _ _ _)
```

### A sum of zeroes is zero

```agda
module _
  {l : Level} (A : Commutative-Ring l)
  where

  sum-zero-Commutative-Ring :
    (n : ℕ) →
    sum-Commutative-Ring A n
      ( zero-fin-sequence-type-Commutative-Ring A n) ＝
    zero-Commutative-Ring A
  sum-zero-Commutative-Ring = sum-zero-Ring (ring-Commutative-Ring A)
```
