# Sums of finite sequences in commutative semirings

```agda
module commutative-algebra.sums-of-finite-sequences-of-elements-commutative-semirings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-semirings

open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import finite-group-theory.permutations-standard-finite-types

open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels

open import linear-algebra.finite-sequences-in-commutative-semirings

open import lists.finite-sequences

open import ring-theory.sums-of-finite-sequences-of-elements-semirings

open import univalent-combinatorics.coproduct-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The
{{#concept "sum operation" Disambiguation="of a finite sequence in a commutative semiring" WD="sum" WDID=Q218005 Agda=sum-fin-sequence-type-Commutative-Semiring}}
extends the binary addition operation on a
[commutative semiring](commutative-algebra.commutative-semirings.md) `R` to any
[finite sequence](lists.finite-sequences.md) of elements of `R`.

## Definition

```agda
sum-fin-sequence-type-Commutative-Semiring :
  {l : Level} (A : Commutative-Semiring l) (n : ℕ) →
  (fin-sequence-type-Commutative-Semiring A n) → type-Commutative-Semiring A
sum-fin-sequence-type-Commutative-Semiring A =
  sum-fin-sequence-type-Semiring (semiring-Commutative-Semiring A)
```

## Properties

### Sums of one and two elements

```agda
module _
  {l : Level} (A : Commutative-Semiring l)
  where

  compute-sum-one-element-Commutative-Semiring :
    (f : fin-sequence-type-Commutative-Semiring A 1) →
    sum-fin-sequence-type-Commutative-Semiring A 1 f ＝ head-fin-sequence 0 f
  compute-sum-one-element-Commutative-Semiring =
    compute-sum-one-element-Semiring (semiring-Commutative-Semiring A)

  compute-sum-two-elements-Commutative-Semiring :
    (f : fin-sequence-type-Commutative-Semiring A 2) →
    sum-fin-sequence-type-Commutative-Semiring A 2 f ＝
    add-Commutative-Semiring A (f (zero-Fin 1)) (f (one-Fin 1))
  compute-sum-two-elements-Commutative-Semiring =
    compute-sum-two-elements-Semiring (semiring-Commutative-Semiring A)
```

### Sums are homotopy invariant

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  htpy-sum-fin-sequence-type-Commutative-Semiring :
    (n : ℕ) {f g : fin-sequence-type-Commutative-Semiring R n} →
    (f ~ g) →
    sum-fin-sequence-type-Commutative-Semiring R n f ＝
    sum-fin-sequence-type-Commutative-Semiring R n g
  htpy-sum-fin-sequence-type-Commutative-Semiring =
    htpy-sum-fin-sequence-type-Semiring (semiring-Commutative-Semiring R)
```

### Sums are equal to the zero-th term plus the rest

```agda
module _
  {l : Level} (A : Commutative-Semiring l)
  where

  cons-sum-fin-sequence-type-Commutative-Semiring :
    (n : ℕ) (f : fin-sequence-type-Commutative-Semiring A (succ-ℕ n)) →
    {x : type-Commutative-Semiring A} → head-fin-sequence n f ＝ x →
    sum-fin-sequence-type-Commutative-Semiring A (succ-ℕ n) f ＝
    add-Commutative-Semiring A
      ( sum-fin-sequence-type-Commutative-Semiring A n (tail-fin-sequence n f))
      ( x)
  cons-sum-fin-sequence-type-Commutative-Semiring =
    cons-sum-fin-sequence-type-Semiring (semiring-Commutative-Semiring A)

  snoc-sum-fin-sequence-type-Commutative-Semiring :
    (n : ℕ) (f : fin-sequence-type-Commutative-Semiring A (succ-ℕ n)) →
    {x : type-Commutative-Semiring A} → f (zero-Fin n) ＝ x →
    sum-fin-sequence-type-Commutative-Semiring A (succ-ℕ n) f ＝
    add-Commutative-Semiring A
      ( x)
      ( sum-fin-sequence-type-Commutative-Semiring A n (f ∘ inr-Fin n))
  snoc-sum-fin-sequence-type-Commutative-Semiring =
    snoc-sum-fin-sequence-type-Semiring (semiring-Commutative-Semiring A)
```

### Multiplication distributes over sums

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  left-distributive-mul-sum-fin-sequence-type-Commutative-Semiring :
    (n : ℕ) (x : type-Commutative-Semiring R)
    (f : fin-sequence-type-Commutative-Semiring R n) →
    mul-Commutative-Semiring
      ( R)
      ( x)
      ( sum-fin-sequence-type-Commutative-Semiring R n f) ＝
    sum-fin-sequence-type-Commutative-Semiring
      ( R)
      ( n)
      ( mul-Commutative-Semiring R x ∘ f)
  left-distributive-mul-sum-fin-sequence-type-Commutative-Semiring =
    left-distributive-mul-sum-fin-sequence-type-Semiring
      ( semiring-Commutative-Semiring R)

  right-distributive-mul-sum-fin-sequence-type-Commutative-Semiring :
    (n : ℕ) (f : fin-sequence-type-Commutative-Semiring R n)
    (x : type-Commutative-Semiring R) →
    mul-Commutative-Semiring
      ( R)
      ( sum-fin-sequence-type-Commutative-Semiring R n f)
      ( x) ＝
    sum-fin-sequence-type-Commutative-Semiring
      ( R)
      ( n)
      ( mul-Commutative-Semiring' R x ∘ f)
  right-distributive-mul-sum-fin-sequence-type-Commutative-Semiring =
    right-distributive-mul-sum-fin-sequence-type-Semiring
      ( semiring-Commutative-Semiring R)
```

### Interchange law of sums and addition in a commutative semiring

```agda
module _
  {l : Level} (A : Commutative-Semiring l)
  where

  interchange-add-sum-fin-sequence-type-Commutative-Semiring :
    (n : ℕ) (f g : fin-sequence-type-Commutative-Semiring A n) →
    add-Commutative-Semiring A
      ( sum-fin-sequence-type-Commutative-Semiring A n f)
      ( sum-fin-sequence-type-Commutative-Semiring A n g) ＝
    sum-fin-sequence-type-Commutative-Semiring A n
      ( add-fin-sequence-type-Commutative-Semiring A n f g)
  interchange-add-sum-fin-sequence-type-Commutative-Semiring =
    interchange-add-sum-fin-sequence-type-Semiring
      ( semiring-Commutative-Semiring A)
```

### Extending a sum of elements in a commutative semiring

```agda
module _
  {l : Level} (A : Commutative-Semiring l)
  where

  extend-sum-fin-sequence-type-Commutative-Semiring :
    (n : ℕ) (f : fin-sequence-type-Commutative-Semiring A n) →
    sum-fin-sequence-type-Commutative-Semiring A
      ( succ-ℕ n)
      ( cons-fin-sequence-type-Commutative-Semiring A n
        ( zero-Commutative-Semiring A) f) ＝
    sum-fin-sequence-type-Commutative-Semiring A n f
  extend-sum-fin-sequence-type-Commutative-Semiring =
    extend-sum-fin-sequence-type-Semiring (semiring-Commutative-Semiring A)
```

### Shifting a sum of elements in a commutative semiring

```agda
module _
  {l : Level} (A : Commutative-Semiring l)
  where

  shift-sum-fin-sequence-type-Commutative-Semiring :
    (n : ℕ) (f : fin-sequence-type-Commutative-Semiring A n) →
    sum-fin-sequence-type-Commutative-Semiring A
      ( succ-ℕ n)
      ( snoc-fin-sequence-type-Commutative-Semiring A n f
        ( zero-Commutative-Semiring A)) ＝
    sum-fin-sequence-type-Commutative-Semiring A n f
  shift-sum-fin-sequence-type-Commutative-Semiring =
    shift-sum-fin-sequence-type-Semiring (semiring-Commutative-Semiring A)
```

### A sum of zeroes is zero

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  sum-zero-fin-sequence-type-Commutative-Semiring :
    (n : ℕ) →
    sum-fin-sequence-type-Commutative-Semiring R n
      ( zero-fin-sequence-type-Commutative-Semiring R n) ＝
    zero-Commutative-Semiring R
  sum-zero-fin-sequence-type-Commutative-Semiring =
    sum-zero-fin-sequence-type-Semiring (semiring-Commutative-Semiring R)
```

### Splitting sums of `n + m` elements into a sum of `n` elements and a sum of `m` elements

```agda
split-sum-fin-sequence-type-Commutative-Semiring :
  {l : Level} (A : Commutative-Semiring l)
  (n m : ℕ) (f : fin-sequence-type-Commutative-Semiring A (n +ℕ m)) →
  sum-fin-sequence-type-Commutative-Semiring A (n +ℕ m) f ＝
  add-Commutative-Semiring A
    ( sum-fin-sequence-type-Commutative-Semiring A
      ( n)
      ( f ∘ inl-coproduct-Fin n m))
    ( sum-fin-sequence-type-Commutative-Semiring A
      ( m)
      ( f ∘ inr-coproduct-Fin n m))
split-sum-fin-sequence-type-Commutative-Semiring A =
  split-sum-fin-sequence-type-Semiring (semiring-Commutative-Semiring A)
```

### Permutations preserve sums

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  preserves-sum-permutation-Commutative-Semiring :
    (n : ℕ) → (σ : Permutation n) →
    (f : fin-sequence-type-Commutative-Semiring R n) →
    sum-fin-sequence-type-Commutative-Semiring R n f ＝
    sum-fin-sequence-type-Commutative-Semiring R n (f ∘ map-equiv σ)
  preserves-sum-permutation-Commutative-Semiring =
    preserves-sum-permutation-fin-sequence-type-Semiring
      ( semiring-Commutative-Semiring R)
```
