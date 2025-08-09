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
open import finite-group-theory.transpositions-standard-finite-types

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.negated-equality
open import foundation.unit-type
open import foundation.universe-levels

open import group-theory.commutative-monoids
open import group-theory.powers-of-elements-commutative-monoids
open import group-theory.sums-of-finite-sequences-of-elements-monoids

open import linear-algebra.finite-sequences-in-commutative-monoids

open import lists.lists

open import univalent-combinatorics.coproduct-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The
{{#concept "sum operation" Disambiguation="of a finite sequence in a commutative monoid" WD="sum" WDID=Q218005 Agda=sum-fin-sequence-type-Commutative-Monoid}}
extends the binary operation on a
[commutative monoid](group-theory.commutative-monoids.md) `M` to any
[finite sequence](lists.finite-sequences.md) of elements of `M`.

## Definition

```agda
sum-fin-sequence-type-Commutative-Monoid :
  {l : Level} (M : Commutative-Monoid l) (n : ℕ) →
  fin-sequence-type-Commutative-Monoid M n → type-Commutative-Monoid M
sum-fin-sequence-type-Commutative-Monoid M =
  sum-fin-sequence-type-Monoid (monoid-Commutative-Monoid M)
```

## Properties

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
    preserves-sum-adjacent-transposition-sum-fin-sequence-type-Commutative-Monoid :
      (n : ℕ) → (k : Fin n) →
      (f : fin-sequence-type-Commutative-Monoid M (succ-ℕ n)) →
      sum-fin-sequence-type-Commutative-Monoid M (succ-ℕ n) f ＝
      sum-fin-sequence-type-Commutative-Monoid
        M (succ-ℕ n) (f ∘ map-adjacent-transposition-Fin n k)
    preserves-sum-adjacent-transposition-sum-fin-sequence-type-Commutative-Monoid
      (succ-ℕ n) (inl x) f =
        ap-mul-Commutative-Monoid
          ( M)
          ( preserves-sum-adjacent-transposition-sum-fin-sequence-type-Commutative-Monoid
            ( n)
            ( x)
            ( f ∘ inl-Fin (succ-ℕ n)))
          ( refl)
    preserves-sum-adjacent-transposition-sum-fin-sequence-type-Commutative-Monoid
      (succ-ℕ n) (inr star) f = right-swap-mul-Commutative-Monoid M _ _ _

    preserves-sum-permutation-list-adjacent-transpositions-Commutative-Monoid :
      (n : ℕ) → (L : list (Fin n)) →
      (f : fin-sequence-type-Commutative-Monoid M (succ-ℕ n)) →
      sum-fin-sequence-type-Commutative-Monoid M (succ-ℕ n) f ＝
      sum-fin-sequence-type-Commutative-Monoid
        M (succ-ℕ n) (f ∘ map-permutation-list-adjacent-transpositions n L)
    preserves-sum-permutation-list-adjacent-transpositions-Commutative-Monoid
      n nil f = refl
    preserves-sum-permutation-list-adjacent-transpositions-Commutative-Monoid
      n (cons x L) f =
        preserves-sum-adjacent-transposition-sum-fin-sequence-type-Commutative-Monoid
          ( n)
          ( x)
          ( f) ∙
        preserves-sum-permutation-list-adjacent-transpositions-Commutative-Monoid
          ( n)
          ( L)
          ( f ∘ map-adjacent-transposition-Fin n x)

    preserves-sum-transposition-Commutative-Monoid :
      (n : ℕ) (i j : Fin (succ-ℕ n)) (neq : i ≠ j) →
      (f : fin-sequence-type-Commutative-Monoid M (succ-ℕ n)) →
      sum-fin-sequence-type-Commutative-Monoid M (succ-ℕ n) f ＝
      sum-fin-sequence-type-Commutative-Monoid
        M (succ-ℕ n) (f ∘ map-transposition-Fin (succ-ℕ n) i j neq)
    preserves-sum-transposition-Commutative-Monoid n i j i≠j f =
      preserves-sum-permutation-list-adjacent-transpositions-Commutative-Monoid
        ( n)
        ( list-adjacent-transpositions-transposition-Fin n i j)
        ( f) ∙
      ap
        ( λ g →
          sum-fin-sequence-type-Commutative-Monoid M
            ( succ-ℕ n)
            ( f ∘ map-equiv g))
        ( eq-permutation-list-adjacent-transpositions-transposition-Fin
          ( n)
          ( i)
          ( j)
          ( i≠j))

    preserves-sum-permutation-list-standard-transpositions-Commutative-Monoid :
      (n : ℕ) → (L : list (Σ (Fin n × Fin n) ( λ (i , j) → i ≠ j))) →
      (f : fin-sequence-type-Commutative-Monoid M n) →
      sum-fin-sequence-type-Commutative-Monoid M n f ＝
      sum-fin-sequence-type-Commutative-Monoid
        M n (f ∘ map-equiv (permutation-list-standard-transpositions-Fin n L))
    preserves-sum-permutation-list-standard-transpositions-Commutative-Monoid
      zero-ℕ _ _ = refl
    preserves-sum-permutation-list-standard-transpositions-Commutative-Monoid
      (succ-ℕ n) nil f = refl
    preserves-sum-permutation-list-standard-transpositions-Commutative-Monoid
      (succ-ℕ n) (cons ((i , j) , i≠j) L) f =
        preserves-sum-transposition-Commutative-Monoid n i j i≠j f ∙
        preserves-sum-permutation-list-standard-transpositions-Commutative-Monoid
          ( succ-ℕ n)
          ( L)
          ( f ∘ map-transposition-Fin (succ-ℕ n) i j i≠j)

    preserves-sum-permutation-fin-sequence-type-Commutative-Monoid :
      (n : ℕ) → (σ : Permutation n) →
      (f : fin-sequence-type-Commutative-Monoid M n) →
      sum-fin-sequence-type-Commutative-Monoid M n f ＝
      sum-fin-sequence-type-Commutative-Monoid M n (f ∘ map-equiv σ)
    preserves-sum-permutation-fin-sequence-type-Commutative-Monoid n σ f =
      preserves-sum-permutation-list-standard-transpositions-Commutative-Monoid
        ( n)
        ( list-standard-transpositions-permutation-Fin n σ)
        ( f) ∙
      ap
        ( λ τ → sum-fin-sequence-type-Commutative-Monoid M n (f ∘ map-equiv τ))
        ( eq-permutation-list-standard-transpositions-Fin n σ)
```

### The sum of a sequence of length `n` of a constant `c` is `n` times `c`

```agda
sum-const-sequence-type-Commutative-Monoid :
  {l : Level} (M : Commutative-Monoid l) (n : ℕ) →
  (c : type-Commutative-Monoid M) →
  sum-fin-sequence-type-Commutative-Monoid M n (λ _ → c) ＝
  power-Commutative-Monoid M n c
sum-const-sequence-type-Commutative-Monoid M =
  sum-const-sequence-type-Monoid (monoid-Commutative-Monoid M)
```

## See also

- [Sums of finite families of elements in commutative monoids](group-theory.sums-of-finite-families-of-elements-commutative-monoids.md)
