# Sums of finite sequences in rings

```agda
module ring-theory.sums-of-finite-sequences-of-elements-rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import finite-group-theory.permutations-standard-finite-types

open import foundation.coproduct-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels

open import linear-algebra.finite-sequences-in-rings

open import lists.finite-sequences

open import ring-theory.rings
open import ring-theory.sums-of-finite-sequences-of-elements-semirings

open import univalent-combinatorics.coproduct-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The
{{#concept "sum operation" Disambiguation="of a finite sequence in a ring" WD="sum" WDID=Q218005 Agda=sum-fin-sequence-type-Ring}}
extends the binary addition operation on a [ring](ring-theory.rings.md) `R` to
any [finite sequence](lists.finite-sequences.md) of elements of `R`.

## Definition

```agda
sum-fin-sequence-type-Ring :
  {l : Level} (R : Ring l) (n : ℕ) → fin-sequence-type-Ring R n → type-Ring R
sum-fin-sequence-type-Ring R = sum-fin-sequence-type-Semiring (semiring-Ring R)
```

## Properties

### Sums of one and two elements

```agda
module _
  {l : Level} (R : Ring l)
  where

  compute-sum-one-element-Ring :
    (f : fin-sequence-type-Ring R 1) →
    sum-fin-sequence-type-Ring R 1 f ＝ head-fin-sequence 0 f
  compute-sum-one-element-Ring =
    compute-sum-one-element-Semiring (semiring-Ring R)

  compute-sum-two-elements-Ring :
    (f : fin-sequence-type-Ring R 2) →
    sum-fin-sequence-type-Ring R 2 f ＝
    add-Ring R (f (zero-Fin 1)) (f (one-Fin 1))
  compute-sum-two-elements-Ring =
    compute-sum-two-elements-Semiring (semiring-Ring R)
```

### Sums are homotopy invariant

```agda
module _
  {l : Level} (R : Ring l)
  where

  htpy-sum-fin-sequence-type-Ring :
    (n : ℕ) {f g : fin-sequence-type-Ring R n} →
    (f ~ g) →
    sum-fin-sequence-type-Ring R n f ＝ sum-fin-sequence-type-Ring R n g
  htpy-sum-fin-sequence-type-Ring =
    htpy-sum-fin-sequence-type-Semiring (semiring-Ring R)
```

### Sums are equal to the zero-th term plus the rest

```agda
module _
  {l : Level} (R : Ring l)
  where

  cons-sum-fin-sequence-type-Ring :
    (n : ℕ) (f : fin-sequence-type-Ring R (succ-ℕ n)) →
    {x : type-Ring R} → head-fin-sequence n f ＝ x →
    sum-fin-sequence-type-Ring R (succ-ℕ n) f ＝
    add-Ring R (sum-fin-sequence-type-Ring R n (tail-fin-sequence n f)) x
  cons-sum-fin-sequence-type-Ring =
    cons-sum-fin-sequence-type-Semiring (semiring-Ring R)

  snoc-sum-fin-sequence-type-Ring :
    (n : ℕ) (f : fin-sequence-type-Ring R (succ-ℕ n)) →
    {x : type-Ring R} → f (zero-Fin n) ＝ x →
    sum-fin-sequence-type-Ring R (succ-ℕ n) f ＝
    add-Ring R
      ( x)
      ( sum-fin-sequence-type-Ring R n (f ∘ inr-Fin n))
  snoc-sum-fin-sequence-type-Ring =
    snoc-sum-fin-sequence-type-Semiring (semiring-Ring R)
```

### Multiplication distributes over sums

```agda
module _
  {l : Level} (R : Ring l)
  where

  left-distributive-mul-sum-fin-sequence-type-Ring :
    (n : ℕ) (x : type-Ring R)
    (f : fin-sequence-type-Ring R n) →
    mul-Ring R x (sum-fin-sequence-type-Ring R n f) ＝
    sum-fin-sequence-type-Ring R n (λ i → mul-Ring R x (f i))
  left-distributive-mul-sum-fin-sequence-type-Ring =
    left-distributive-mul-sum-fin-sequence-type-Semiring (semiring-Ring R)

  right-distributive-mul-sum-fin-sequence-type-Ring :
    (n : ℕ) (f : fin-sequence-type-Ring R n)
    (x : type-Ring R) →
    mul-Ring R (sum-fin-sequence-type-Ring R n f) x ＝
    sum-fin-sequence-type-Ring R n (λ i → mul-Ring R (f i) x)
  right-distributive-mul-sum-fin-sequence-type-Ring =
    right-distributive-mul-sum-fin-sequence-type-Semiring (semiring-Ring R)
```

### Interchange law of sums and addition in a semiring

```agda
module _
  {l : Level} (R : Ring l)
  where

  interchange-add-sum-fin-sequence-type-Ring :
    (n : ℕ) (f g : fin-sequence-type-Ring R n) →
    add-Ring R
      ( sum-fin-sequence-type-Ring R n f)
      ( sum-fin-sequence-type-Ring R n g) ＝
    sum-fin-sequence-type-Ring R n
      ( add-fin-sequence-type-Ring R n f g)
  interchange-add-sum-fin-sequence-type-Ring =
    interchange-add-sum-fin-sequence-type-Semiring (semiring-Ring R)
```

### Extending a sum of elements in a semiring

```agda
module _
  {l : Level} (R : Ring l)
  where

  extend-sum-fin-sequence-type-Ring :
    (n : ℕ) (f : fin-sequence-type-Ring R n) →
    sum-fin-sequence-type-Ring R
      ( succ-ℕ n)
      ( cons-fin-sequence-type-Ring R n (zero-Ring R) f) ＝
    sum-fin-sequence-type-Ring R n f
  extend-sum-fin-sequence-type-Ring =
    extend-sum-fin-sequence-type-Semiring (semiring-Ring R)
```

### Shifting a sum of elements in a semiring

```agda
module _
  {l : Level} (R : Ring l)
  where

  shift-sum-fin-sequence-type-Ring :
    (n : ℕ) (f : fin-sequence-type-Ring R n) →
    sum-fin-sequence-type-Ring R
      ( succ-ℕ n)
      ( snoc-fin-sequence-type-Ring R n f
        ( zero-Ring R)) ＝
    sum-fin-sequence-type-Ring R n f
  shift-sum-fin-sequence-type-Ring =
    shift-sum-fin-sequence-type-Semiring (semiring-Ring R)
```

### A sum of zeroes is zero

```agda
module _
  {l : Level} (R : Ring l)
  where

  sum-zero-fin-sequence-type-Ring :
    (n : ℕ) →
    sum-fin-sequence-type-Ring R n (zero-fin-sequence-type-Ring R n) ＝
    zero-Ring R
  sum-zero-fin-sequence-type-Ring =
    sum-zero-fin-sequence-type-Semiring (semiring-Ring R)
```

### Splitting sums of `n + m` elements into a sum of `n` elements and a sum of `m` elements

```agda
split-sum-fin-sequence-type-Ring :
  {l : Level} (R : Ring l)
  (n m : ℕ) (f : fin-sequence-type-Ring R (n +ℕ m)) →
  sum-fin-sequence-type-Ring R (n +ℕ m) f ＝
  add-Ring R
    ( sum-fin-sequence-type-Ring R n (f ∘ inl-coproduct-Fin n m))
    ( sum-fin-sequence-type-Ring R m (f ∘ inr-coproduct-Fin n m))
split-sum-fin-sequence-type-Ring R =
  split-sum-fin-sequence-type-Semiring (semiring-Ring R)
```

### Permutations preserve sums

```agda
module _
  {l : Level} (R : Ring l)
  where

  preserves-sum-permutation-fin-sequence-type-Ring :
    (n : ℕ) → (σ : Permutation n) →
    (f : fin-sequence-type-Ring R n) →
    sum-fin-sequence-type-Ring R n f ＝
    sum-fin-sequence-type-Ring R n (f ∘ map-equiv σ)
  preserves-sum-permutation-fin-sequence-type-Ring =
    preserves-sum-permutation-fin-sequence-type-Semiring (semiring-Ring R)
```

## See also

- [Sums of finite families of elements in rings](ring-theory.sums-of-finite-families-of-elements-rings.md)
