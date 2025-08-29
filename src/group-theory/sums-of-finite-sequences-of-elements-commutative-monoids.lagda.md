# Sums of finite sequences of elements in commutative monoids

```agda
{-# OPTIONS --lossy-unification #-}

module group-theory.sums-of-finite-sequences-of-elements-commutative-monoids where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import finite-group-theory.permutations-standard-finite-types

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.commutative-monoids
open import group-theory.sums-of-finite-sequences-of-elements-commutative-semigroups
open import group-theory.sums-of-finite-sequences-of-elements-monoids

open import linear-algebra.finite-sequences-in-commutative-monoids

open import univalent-combinatorics.coproduct-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The
{{#concept "sum operation" Disambiguation="of a finite sequence in a commutative monoid" WD="sum" WDID=Q218005 Agda=sum-fin-sequence-type-Commutative-Monoid}}
extends the binary operation on a
[commutative monoid](group-theory.commutative-monoids.md) `M` to any
[finite sequence](lists.finite-sequences.md) of elements of `M`.

We use additive terminology consistently with the linear algebra definition of
[finite sequences in commutative monoids](linear-algebra.finite-sequences-in-commutative-monoids.md)
despite the use of multiplicative terminology for commutative monoids in
general.

## Definition

```agda
sum-fin-sequence-type-Commutative-Monoid :
  {l : Level} (M : Commutative-Monoid l) (n : ℕ) →
  fin-sequence-type-Commutative-Monoid M n → type-Commutative-Monoid M
sum-fin-sequence-type-Commutative-Monoid M =
  sum-fin-sequence-type-Monoid (monoid-Commutative-Monoid M)
```

## Properties

#### Sums in a commutative monoid equal sums in the corresponding commutative semigroup

```agda
module _
  {l : Level} (M : Commutative-Monoid l)
  where

  eq-sum-commutative-semigroup-sum-fin-sequence-type-Commutative-Monoid :
    (n : ℕ) (f : fin-sequence-type-Commutative-Monoid M (succ-ℕ n)) →
    sum-fin-sequence-type-Commutative-Monoid M (succ-ℕ n) f ＝
    sum-fin-sequence-type-Commutative-Semigroup
      ( commutative-semigroup-Commutative-Monoid M)
      ( n)
      ( f)
  eq-sum-commutative-semigroup-sum-fin-sequence-type-Commutative-Monoid
    zero-ℕ f = left-unit-law-mul-Commutative-Monoid M _
  eq-sum-commutative-semigroup-sum-fin-sequence-type-Commutative-Monoid
    (succ-ℕ n) f =
      ap
        ( mul-Commutative-Monoid' M _)
        ( eq-sum-commutative-semigroup-sum-fin-sequence-type-Commutative-Monoid
          ( n)
          ( f ∘ inl))
```

### Sums of one and two elements

```agda
module _
  {l : Level} (M : Commutative-Monoid l)
  where

  compute-sum-one-element-Commutative-Monoid :
    (f : fin-sequence-type-Commutative-Monoid M 1) →
    sum-fin-sequence-type-Commutative-Monoid M 1 f ＝
    head-fin-sequence-type-Commutative-Monoid M 0 f
  compute-sum-one-element-Commutative-Monoid =
    compute-sum-one-element-Monoid (monoid-Commutative-Monoid M)

  compute-sum-two-elements-Commutative-Monoid :
    (f : fin-sequence-type-Commutative-Monoid M 2) →
    sum-fin-sequence-type-Commutative-Monoid M 2 f ＝
    mul-Commutative-Monoid M (f (zero-Fin 1)) (f (one-Fin 1))
  compute-sum-two-elements-Commutative-Monoid =
    compute-sum-two-elements-Monoid (monoid-Commutative-Monoid M)
```

### Sums are homotopy invariant

```agda
module _
  {l : Level} (M : Commutative-Monoid l)
  where

  htpy-sum-fin-sequence-type-Commutative-Monoid :
    (n : ℕ) {f g : fin-sequence-type-Commutative-Monoid M n} →
    (f ~ g) →
    sum-fin-sequence-type-Commutative-Monoid M n f ＝
    sum-fin-sequence-type-Commutative-Monoid M n g
  htpy-sum-fin-sequence-type-Commutative-Monoid =
    htpy-sum-fin-sequence-type-Monoid (monoid-Commutative-Monoid M)
```

### Sums are equal to the zero-th term plus the rest

```agda
module _
  {l : Level} (M : Commutative-Monoid l)
  where

  cons-sum-fin-sequence-type-Commutative-Monoid :
    (n : ℕ) (f : fin-sequence-type-Commutative-Monoid M (succ-ℕ n)) →
    {x : type-Commutative-Monoid M} →
    head-fin-sequence-type-Commutative-Monoid M n f ＝ x →
    sum-fin-sequence-type-Commutative-Monoid M (succ-ℕ n) f ＝
    mul-Commutative-Monoid M
      ( sum-fin-sequence-type-Commutative-Monoid M n (f ∘ inl-Fin n))
      ( x)
  cons-sum-fin-sequence-type-Commutative-Monoid =
    cons-sum-fin-sequence-type-Monoid (monoid-Commutative-Monoid M)

  snoc-sum-fin-sequence-type-Commutative-Monoid :
    (n : ℕ) (f : fin-sequence-type-Commutative-Monoid M (succ-ℕ n)) →
    {x : type-Commutative-Monoid M} → f (zero-Fin n) ＝ x →
    sum-fin-sequence-type-Commutative-Monoid M (succ-ℕ n) f ＝
    mul-Commutative-Monoid M
      ( x)
      ( sum-fin-sequence-type-Commutative-Monoid M n (f ∘ inr-Fin n))
  snoc-sum-fin-sequence-type-Commutative-Monoid =
    snoc-sum-fin-sequence-type-Monoid (monoid-Commutative-Monoid M)
```

### Extending a sum of elements in a monoid

```agda
module _
  {l : Level} (M : Commutative-Monoid l)
  where

  extend-sum-fin-sequence-type-Commutative-Monoid :
    (n : ℕ) (f : fin-sequence-type-Commutative-Monoid M n) →
    sum-fin-sequence-type-Commutative-Monoid M
      ( succ-ℕ n)
      ( cons-fin-sequence-type-Commutative-Monoid
        ( M)
        ( n)
        ( unit-Commutative-Monoid M) f) ＝
    sum-fin-sequence-type-Commutative-Monoid M n f
  extend-sum-fin-sequence-type-Commutative-Monoid =
    extend-sum-fin-sequence-type-Monoid (monoid-Commutative-Monoid M)
```

### Shifting a sum of elements in a monoid

```agda
module _
  {l : Level} (M : Commutative-Monoid l)
  where

  shift-sum-fin-sequence-type-Commutative-Monoid :
    (n : ℕ) (f : fin-sequence-type-Commutative-Monoid M n) →
    sum-fin-sequence-type-Commutative-Monoid M
      ( succ-ℕ n)
      ( snoc-fin-sequence-type-Commutative-Monoid M n f
        ( unit-Commutative-Monoid M)) ＝
    sum-fin-sequence-type-Commutative-Monoid M n f
  shift-sum-fin-sequence-type-Commutative-Monoid =
    shift-sum-fin-sequence-type-Monoid (monoid-Commutative-Monoid M)
```

### A sum of zeroes is zero

```agda
module _
  {l : Level} (M : Commutative-Monoid l)
  where

  sum-zero-fin-sequence-type-Commutative-Monoid :
    (n : ℕ) →
    sum-fin-sequence-type-Commutative-Monoid
      ( M)
      ( n)
      ( zero-fin-sequence-type-Commutative-Monoid M n) ＝
    unit-Commutative-Monoid M
  sum-zero-fin-sequence-type-Commutative-Monoid =
    sum-zero-fin-sequence-type-Monoid (monoid-Commutative-Monoid M)
```

### Splitting sums of `n + m` elements into a sum of `n` elements and a sum of `m` elements

```agda
split-sum-fin-sequence-type-Commutative-Monoid :
  {l : Level} (M : Commutative-Monoid l)
  (n m : ℕ) (f : fin-sequence-type-Commutative-Monoid M (n +ℕ m)) →
  sum-fin-sequence-type-Commutative-Monoid M (n +ℕ m) f ＝
  mul-Commutative-Monoid M
    ( sum-fin-sequence-type-Commutative-Monoid M n (f ∘ inl-coproduct-Fin n m))
    ( sum-fin-sequence-type-Commutative-Monoid M m (f ∘ inr-coproduct-Fin n m))
split-sum-fin-sequence-type-Commutative-Monoid M =
  split-sum-fin-sequence-type-Monoid (monoid-Commutative-Monoid M)
```

### Permutations preserve sums

```agda
module _
  {l : Level} (M : Commutative-Monoid l)
  where

  abstract
    preserves-sum-permutation-fin-sequence-type-Commutative-Monoid :
      (n : ℕ) → (σ : Permutation n) →
      (f : fin-sequence-type-Commutative-Monoid M n) →
      sum-fin-sequence-type-Commutative-Monoid M n f ＝
      sum-fin-sequence-type-Commutative-Monoid M n (f ∘ map-equiv σ)
    preserves-sum-permutation-fin-sequence-type-Commutative-Monoid zero-ℕ _ f =
      refl
    preserves-sum-permutation-fin-sequence-type-Commutative-Monoid
      (succ-ℕ n) σ f =
        eq-sum-commutative-semigroup-sum-fin-sequence-type-Commutative-Monoid
          ( M)
          ( n)
          ( f) ∙
        preserves-sum-permutation-fin-sequence-type-Commutative-Semigroup
          ( commutative-semigroup-Commutative-Monoid M)
          ( n)
          ( σ)
          ( f) ∙
        inv
          ( eq-sum-commutative-semigroup-sum-fin-sequence-type-Commutative-Monoid
            ( M)
            ( n)
            ( f ∘ map-equiv σ))
```

## See also

- [Sums of finite families of elements in commutative monoids](group-theory.sums-of-finite-families-of-elements-commutative-monoids.md)
