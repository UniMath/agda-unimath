# Sums of finite sequences in commutative rings

```agda
module commutative-algebra.sums-of-finite-sequences-of-elements-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings
open import commutative-algebra.multiples-of-elements-commutative-rings

open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import finite-group-theory.permutations-standard-finite-types

open import foundation.coproduct-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels

open import linear-algebra.finite-sequences-in-commutative-rings

open import lists.finite-sequences

open import ring-theory.sums-of-finite-sequences-of-elements-rings

open import univalent-combinatorics.coproduct-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The
{{#concept "sum operation" Disambiguation="of a finite sequence in a commutative ring" WD="sum" WDID=Q218005 Agda=sum-fin-sequence-type-Commutative-Ring}}
extends the binary addition operation on a
[commutative ring](commutative-algebra.commutative-rings.md) `A` to any
[finite sequence](lists.finite-sequences.md) of elements of `A`.

## Definition

```agda
sum-fin-sequence-type-Commutative-Ring :
  {l : Level} (A : Commutative-Ring l) (n : ℕ) →
  (fin-sequence-type-Commutative-Ring A n) → type-Commutative-Ring A
sum-fin-sequence-type-Commutative-Ring A =
  sum-fin-sequence-type-Ring (ring-Commutative-Ring A)
```

## Properties

### Sums of one and two elements

```agda
module _
  {l : Level} (A : Commutative-Ring l)
  where

  compute-sum-one-element-Commutative-Ring :
    (f : fin-sequence-type-Commutative-Ring A 1) →
    sum-fin-sequence-type-Commutative-Ring A 1 f ＝ head-fin-sequence 0 f
  compute-sum-one-element-Commutative-Ring =
    compute-sum-one-element-Ring (ring-Commutative-Ring A)

  compute-sum-two-elements-Commutative-Ring :
    (f : fin-sequence-type-Commutative-Ring A 2) →
    sum-fin-sequence-type-Commutative-Ring A 2 f ＝
    add-Commutative-Ring A (f (zero-Fin 1)) (f (one-Fin 1))
  compute-sum-two-elements-Commutative-Ring =
    compute-sum-two-elements-Ring (ring-Commutative-Ring A)
```

### Sums are homotopy invariant

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  htpy-sum-fin-sequence-type-Commutative-Ring :
    (n : ℕ) {f g : fin-sequence-type-Commutative-Ring R n} →
    (f ~ g) →
    sum-fin-sequence-type-Commutative-Ring R n f ＝
    sum-fin-sequence-type-Commutative-Ring R n g
  htpy-sum-fin-sequence-type-Commutative-Ring =
    htpy-sum-fin-sequence-type-Ring (ring-Commutative-Ring R)
```

### Sums are equal to the zero-th term plus the rest

```agda
module _
  {l : Level} (A : Commutative-Ring l)
  where

  abstract
    cons-sum-fin-sequence-type-Commutative-Ring :
      (n : ℕ) (f : fin-sequence-type-Commutative-Ring A (succ-ℕ n)) →
      sum-fin-sequence-type-Commutative-Ring A (succ-ℕ n) f ＝
      add-Commutative-Ring A
        ( sum-fin-sequence-type-Commutative-Ring A n (tail-fin-sequence n f))
        ( head-fin-sequence n f)
    cons-sum-fin-sequence-type-Commutative-Ring =
      cons-sum-fin-sequence-type-Ring (ring-Commutative-Ring A)

    snoc-sum-fin-sequence-type-Commutative-Ring :
      (n : ℕ) (f : fin-sequence-type-Commutative-Ring A (succ-ℕ n)) →
      sum-fin-sequence-type-Commutative-Ring A (succ-ℕ n) f ＝
      add-Commutative-Ring A
        ( f (zero-Fin n))
        ( sum-fin-sequence-type-Commutative-Ring A n (f ∘ inr-Fin n))
    snoc-sum-fin-sequence-type-Commutative-Ring =
      snoc-sum-fin-sequence-type-Ring (ring-Commutative-Ring A)
```

### Multiplication distributes over sums

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  abstract
    left-distributive-mul-sum-fin-sequence-type-Commutative-Ring :
      (n : ℕ) (x : type-Commutative-Ring R)
      (f : fin-sequence-type-Commutative-Ring R n) →
      mul-Commutative-Ring R x (sum-fin-sequence-type-Commutative-Ring R n f) ＝
      sum-fin-sequence-type-Commutative-Ring R n (mul-Commutative-Ring R x ∘ f)
    left-distributive-mul-sum-fin-sequence-type-Commutative-Ring =
      left-distributive-mul-sum-fin-sequence-type-Ring (ring-Commutative-Ring R)

    right-distributive-mul-sum-fin-sequence-type-Commutative-Ring :
      (n : ℕ) (f : fin-sequence-type-Commutative-Ring R n)
      (x : type-Commutative-Ring R) →
      mul-Commutative-Ring R (sum-fin-sequence-type-Commutative-Ring R n f) x ＝
      sum-fin-sequence-type-Commutative-Ring R n (mul-Commutative-Ring' R x ∘ f)
    right-distributive-mul-sum-fin-sequence-type-Commutative-Ring =
      right-distributive-mul-sum-fin-sequence-type-Ring
        ( ring-Commutative-Ring R)
```

### Interchange law of sums and addition in a commutative ring

```agda
module _
  {l : Level} (A : Commutative-Ring l)
  where

  abstract
    interchange-add-sum-fin-sequence-type-Commutative-Ring :
      (n : ℕ) (f g : fin-sequence-type-Commutative-Ring A n) →
      add-Commutative-Ring A
        ( sum-fin-sequence-type-Commutative-Ring A n f)
        ( sum-fin-sequence-type-Commutative-Ring A n g) ＝
      sum-fin-sequence-type-Commutative-Ring A n
        ( add-fin-sequence-type-Commutative-Ring A n f g)
    interchange-add-sum-fin-sequence-type-Commutative-Ring =
      interchange-add-sum-fin-sequence-type-Ring (ring-Commutative-Ring A)
```

### Extending a sum of elements in a commutative ring

```agda
module _
  {l : Level} (A : Commutative-Ring l)
  where

  abstract
    extend-sum-fin-sequence-type-Commutative-Ring :
      (n : ℕ) (f : fin-sequence-type-Commutative-Ring A n) →
      sum-fin-sequence-type-Commutative-Ring A
        ( succ-ℕ n)
        ( cons-fin-sequence-type-Commutative-Ring
          ( A)
          ( n)
          ( zero-Commutative-Ring A)
          ( f)) ＝
      sum-fin-sequence-type-Commutative-Ring A n f
    extend-sum-fin-sequence-type-Commutative-Ring =
      extend-sum-fin-sequence-type-Ring (ring-Commutative-Ring A)
```

### Shifting a sum of elements in a commutative ring

```agda
module _
  {l : Level} (A : Commutative-Ring l)
  where

  abstract
    shift-sum-fin-sequence-type-Commutative-Ring :
      (n : ℕ) (f : fin-sequence-type-Commutative-Ring A n) →
      sum-fin-sequence-type-Commutative-Ring A
        ( succ-ℕ n)
        ( snoc-fin-sequence-type-Commutative-Ring A n f
          ( zero-Commutative-Ring A)) ＝
      sum-fin-sequence-type-Commutative-Ring A n f
    shift-sum-fin-sequence-type-Commutative-Ring =
      shift-sum-fin-sequence-type-Ring (ring-Commutative-Ring A)
```

### Splitting sums of `n + m` elements into a sum of `n` elements and a sum of `m` elements

```agda
abstract
  split-sum-fin-sequence-type-Commutative-Ring :
    {l : Level} (A : Commutative-Ring l)
    (n m : ℕ) (f : fin-sequence-type-Commutative-Ring A (n +ℕ m)) →
    sum-fin-sequence-type-Commutative-Ring A (n +ℕ m) f ＝
    add-Commutative-Ring A
      ( sum-fin-sequence-type-Commutative-Ring A n (f ∘ inl-coproduct-Fin n m))
      ( sum-fin-sequence-type-Commutative-Ring A m (f ∘ inr-coproduct-Fin n m))
  split-sum-fin-sequence-type-Commutative-Ring A =
    split-sum-fin-sequence-type-Ring (ring-Commutative-Ring A)
```

### A sum of zeroes is zero

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  abstract
    sum-zero-fin-sequence-type-Commutative-Ring :
      (n : ℕ) →
      sum-fin-sequence-type-Commutative-Ring R n
        ( zero-fin-sequence-type-Commutative-Ring R n) ＝
      zero-Commutative-Ring R
    sum-zero-fin-sequence-type-Commutative-Ring =
      sum-zero-fin-sequence-type-Ring (ring-Commutative-Ring R)
```

### Permutations preserve sums

```agda
module _
  {l : Level} (A : Commutative-Ring l)
  where

  abstract
    preserves-sum-permutation-fin-sequence-type-Commutative-Ring :
      (n : ℕ) → (σ : Permutation n) →
      (f : fin-sequence-type-Commutative-Ring A n) →
      sum-fin-sequence-type-Commutative-Ring A n f ＝
      sum-fin-sequence-type-Commutative-Ring A n (f ∘ map-equiv σ)
    preserves-sum-permutation-fin-sequence-type-Commutative-Ring =
      preserves-sum-permutation-fin-sequence-type-Ring (ring-Commutative-Ring A)
```

### The sum of a constant finite sequence in a commutative ring is scalar multiplication by the length of the sequence

```agda
abstract
  sum-constant-fin-sequence-type-Commutative-Ring :
    {l : Level} (R : Commutative-Ring l) (n : ℕ) →
    (x : type-Commutative-Ring R) →
    sum-fin-sequence-type-Commutative-Ring R n (λ _ → x) ＝
    multiple-Commutative-Ring R n x
  sum-constant-fin-sequence-type-Commutative-Ring R =
    sum-constant-fin-sequence-type-Ring (ring-Commutative-Ring R)
```

## See also

- [Sums of finite families of elements in commutative rings](commutative-algebra.sums-of-finite-families-of-elements-commutative-rings.md)
