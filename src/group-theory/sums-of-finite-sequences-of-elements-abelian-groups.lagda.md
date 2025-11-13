# Sums of finite sequences of elements in abelian groups

```agda
{-# OPTIONS --lossy-unification #-}

module group-theory.sums-of-finite-sequences-of-elements-abelian-groups where
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

open import group-theory.abelian-groups
open import group-theory.commutative-monoids
open import group-theory.multiples-of-elements-abelian-groups
open import group-theory.sums-of-finite-sequences-of-elements-commutative-monoids
open import group-theory.sums-of-finite-sequences-of-elements-commutative-semigroups
open import group-theory.sums-of-finite-sequences-of-elements-groups

open import linear-algebra.finite-sequences-in-abelian-groups
open import linear-algebra.finite-sequences-in-commutative-monoids

open import univalent-combinatorics.coproduct-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The
{{#concept "sum operation" Disambiguation="of a finite sequence in a abelian group" WD="sum" WDID=Q218005 Agda=sum-fin-sequence-type-Ab}}
extends the binary operation on a
[abelian group](group-theory.commutative-monoids.md) `G` to any
[finite sequence](lists.finite-sequences.md) of elements of `G`.

## Definition

```agda
sum-fin-sequence-type-Ab :
  {l : Level} (G : Ab l) (n : ℕ) →
  fin-sequence-type-Ab G n → type-Ab G
sum-fin-sequence-type-Ab G =
  sum-fin-sequence-type-Commutative-Monoid (commutative-monoid-Ab G)
```

## Properties

### Sums of one and two elements

```agda
module _
  {l : Level} (G : Ab l)
  where

  compute-sum-one-element-Ab :
    (f : fin-sequence-type-Ab G 1) →
    sum-fin-sequence-type-Ab G 1 f ＝
    head-fin-sequence-type-Ab G 0 f
  compute-sum-one-element-Ab =
    compute-sum-one-element-Commutative-Monoid (commutative-monoid-Ab G)

  compute-sum-two-elements-Ab :
    (f : fin-sequence-type-Ab G 2) →
    sum-fin-sequence-type-Ab G 2 f ＝
    add-Ab G (f (zero-Fin 1)) (f (one-Fin 1))
  compute-sum-two-elements-Ab =
    compute-sum-two-elements-Commutative-Monoid (commutative-monoid-Ab G)
```

### Sums are homotopy invariant

```agda
module _
  {l : Level} (G : Ab l)
  where

  htpy-sum-fin-sequence-type-Ab :
    (n : ℕ) {f g : fin-sequence-type-Ab G n} →
    (f ~ g) →
    sum-fin-sequence-type-Ab G n f ＝
    sum-fin-sequence-type-Ab G n g
  htpy-sum-fin-sequence-type-Ab =
    htpy-sum-fin-sequence-type-Commutative-Monoid (commutative-monoid-Ab G)
```

### Sums are equal to the zero-th term plus the rest

```agda
module _
  {l : Level} (G : Ab l)
  where

  cons-sum-fin-sequence-type-Ab :
    (n : ℕ) (f : fin-sequence-type-Ab G (succ-ℕ n)) →
    {x : type-Ab G} →
    head-fin-sequence-type-Ab G n f ＝ x →
    sum-fin-sequence-type-Ab G (succ-ℕ n) f ＝
    add-Ab G
      ( sum-fin-sequence-type-Ab G n (f ∘ inl-Fin n))
      ( x)
  cons-sum-fin-sequence-type-Ab =
    cons-sum-fin-sequence-type-Commutative-Monoid (commutative-monoid-Ab G)

  snoc-sum-fin-sequence-type-Ab :
    (n : ℕ) (f : fin-sequence-type-Ab G (succ-ℕ n)) →
    {x : type-Ab G} → f (zero-Fin n) ＝ x →
    sum-fin-sequence-type-Ab G (succ-ℕ n) f ＝
    add-Ab G
      ( x)
      ( sum-fin-sequence-type-Ab G n (f ∘ inr-Fin n))
  snoc-sum-fin-sequence-type-Ab =
    snoc-sum-fin-sequence-type-Commutative-Monoid (commutative-monoid-Ab G)
```

### Extending a sum of elements in a monoid

```agda
module _
  {l : Level} (G : Ab l)
  where

  extend-sum-fin-sequence-type-Ab :
    (n : ℕ) (f : fin-sequence-type-Ab G n) →
    sum-fin-sequence-type-Ab G
      ( succ-ℕ n)
      ( cons-fin-sequence-type-Ab
        ( G)
        ( n)
        ( zero-Ab G) f) ＝
    sum-fin-sequence-type-Ab G n f
  extend-sum-fin-sequence-type-Ab =
    extend-sum-fin-sequence-type-Commutative-Monoid (commutative-monoid-Ab G)
```

### Shifting a sum of elements in a monoid

```agda
module _
  {l : Level} (G : Ab l)
  where

  shift-sum-fin-sequence-type-Ab :
    (n : ℕ) (f : fin-sequence-type-Ab G n) →
    sum-fin-sequence-type-Ab G
      ( succ-ℕ n)
      ( snoc-fin-sequence-type-Ab G n f
        ( zero-Ab G)) ＝
    sum-fin-sequence-type-Ab G n f
  shift-sum-fin-sequence-type-Ab =
    shift-sum-fin-sequence-type-Commutative-Monoid (commutative-monoid-Ab G)
```

### A sum of zeroes is zero

```agda
module _
  {l : Level} (G : Ab l)
  where

  sum-zero-fin-sequence-type-Ab :
    (n : ℕ) →
    sum-fin-sequence-type-Ab
      ( G)
      ( n)
      ( zero-fin-sequence-type-Ab G n) ＝
    zero-Ab G
  sum-zero-fin-sequence-type-Ab =
    sum-zero-fin-sequence-type-Commutative-Monoid (commutative-monoid-Ab G)
```

### Splitting sums of `n + m` elements into a sum of `n` elements and a sum of `m` elements

```agda
split-sum-fin-sequence-type-Ab :
  {l : Level} (G : Ab l)
  (n m : ℕ) (f : fin-sequence-type-Ab G (n +ℕ m)) →
  sum-fin-sequence-type-Ab G (n +ℕ m) f ＝
  add-Ab G
    ( sum-fin-sequence-type-Ab G n (f ∘ inl-coproduct-Fin n m))
    ( sum-fin-sequence-type-Ab G m (f ∘ inr-coproduct-Fin n m))
split-sum-fin-sequence-type-Ab G =
  split-sum-fin-sequence-type-Commutative-Monoid (commutative-monoid-Ab G)
```

### Permutations preserve sums

```agda
module _
  {l : Level} (G : Ab l)
  where

  abstract
    preserves-sum-permutation-fin-sequence-type-Ab :
      (n : ℕ) → (σ : Permutation n) →
      (f : fin-sequence-type-Ab G n) →
      sum-fin-sequence-type-Ab G n f ＝
      sum-fin-sequence-type-Ab G n (f ∘ map-equiv σ)
    preserves-sum-permutation-fin-sequence-type-Ab =
      preserves-sum-permutation-fin-sequence-type-Commutative-Monoid
        ( commutative-monoid-Ab G)
```

### Constant sums are multiples

```agda
abstract
  constant-sum-fin-sequence-type-Ab :
    {l : Level} (G : Ab l) (n : ℕ) (x : type-Ab G) →
    sum-fin-sequence-type-Ab G n (λ _ → x) ＝ multiple-Ab G n x
  constant-sum-fin-sequence-type-Ab G =
    constant-sum-fin-sequence-type-Group (group-Ab G)
```

## See also

- [Sums of finite families of elements in abelian groups](group-theory.sums-of-finite-families-of-elements-commutative-monoids.md)
