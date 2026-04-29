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
open import group-theory.function-abelian-groups
open import group-theory.homomorphisms-abelian-groups
open import group-theory.multiples-of-elements-abelian-groups
open import group-theory.products-of-finite-sequences-of-elements-commutative-monoids
open import group-theory.products-of-finite-sequences-of-elements-commutative-semigroups
open import group-theory.products-of-finite-sequences-of-elements-groups

open import linear-algebra.finite-sequences-in-abelian-groups
open import linear-algebra.finite-sequences-in-commutative-monoids

open import lists.finite-sequences
open import lists.pairs-of-successive-elements-finite-sequences

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
  product-fin-sequence-type-Commutative-Monoid (commutative-monoid-Ab G)
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
    compute-product-one-element-Commutative-Monoid (commutative-monoid-Ab G)

  compute-sum-two-elements-Ab :
    (f : fin-sequence-type-Ab G 2) →
    sum-fin-sequence-type-Ab G 2 f ＝
    add-Ab G (f (zero-Fin 1)) (f (one-Fin 1))
  compute-sum-two-elements-Ab =
    compute-product-two-elements-Commutative-Monoid (commutative-monoid-Ab G)
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
    htpy-product-fin-sequence-type-Commutative-Monoid (commutative-monoid-Ab G)
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
    cons-product-fin-sequence-type-Commutative-Monoid (commutative-monoid-Ab G)

  snoc-sum-fin-sequence-type-Ab :
    (n : ℕ) (f : fin-sequence-type-Ab G (succ-ℕ n)) →
    {x : type-Ab G} → f (zero-Fin n) ＝ x →
    sum-fin-sequence-type-Ab G (succ-ℕ n) f ＝
    add-Ab G
      ( x)
      ( sum-fin-sequence-type-Ab G n (f ∘ inr-Fin n))
  snoc-sum-fin-sequence-type-Ab =
    snoc-product-fin-sequence-type-Commutative-Monoid (commutative-monoid-Ab G)
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
    extend-product-fin-sequence-type-Commutative-Monoid
      ( commutative-monoid-Ab G)
```

### Shifting a sum of elements in an abelian group

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
    shift-product-fin-sequence-type-Commutative-Monoid (commutative-monoid-Ab G)
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
    product-unit-fin-sequence-type-Commutative-Monoid (commutative-monoid-Ab G)
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
  split-product-fin-sequence-type-Commutative-Monoid (commutative-monoid-Ab G)
```

### Permutations preserve sums

```agda
module _
  {l : Level} (G : Ab l)
  where

  abstract
    preserves-sum-permutation-fin-sequence-type-Ab :
      (n : ℕ) (σ : Permutation n) (f : fin-sequence-type-Ab G n) →
      sum-fin-sequence-type-Ab G n f ＝
      sum-fin-sequence-type-Ab G n (f ∘ map-equiv σ)
    preserves-sum-permutation-fin-sequence-type-Ab =
      preserves-product-permutation-fin-sequence-type-Commutative-Monoid
        ( commutative-monoid-Ab G)
```

### Constant sums are multiples

```agda
abstract
  sum-constant-fin-sequence-type-Ab :
    {l : Level} (G : Ab l) (n : ℕ) (x : type-Ab G) →
    sum-fin-sequence-type-Ab G n (λ _ → x) ＝ multiple-Ab G n x
  sum-constant-fin-sequence-type-Ab G =
    product-constant-fin-sequence-type-Group (group-Ab G)
```

### Interchanging sums and addition

```agda
module _
  {l : Level}
  (G : Ab l)
  where

  abstract
    interchange-sum-add-fin-sequence-type-Ab :
      (n : ℕ) (f g : fin-sequence-type-Ab G n) →
      sum-fin-sequence-type-Ab G n (λ i → add-Ab G (f i) (g i)) ＝
      add-Ab G (sum-fin-sequence-type-Ab G n f) (sum-fin-sequence-type-Ab G n g)
    interchange-sum-add-fin-sequence-type-Ab =
      interchange-product-mul-fin-sequence-type-Commutative-Monoid
        ( commutative-monoid-Ab G)
```

### The sum operation is an abelian group homomorphism

```agda
hom-sum-fin-sequence-type-Ab :
  {l : Level} (G : Ab l) (n : ℕ) →
  hom-Ab (function-Ab G (Fin n)) G
hom-sum-fin-sequence-type-Ab G n =
  ( sum-fin-sequence-type-Ab G n ,
    interchange-sum-add-fin-sequence-type-Ab G n _ _)
```

### Negation distributes over sums

```agda
abstract
  distributive-neg-sum-fin-sequence-type-Ab :
    {l : Level} (G : Ab l) (n : ℕ) (u : fin-sequence-type-Ab G n) →
    neg-Ab G (sum-fin-sequence-type-Ab G n u) ＝
    sum-fin-sequence-type-Ab G n (neg-Ab G ∘ u)
  distributive-neg-sum-fin-sequence-type-Ab G n u =
    inv
      ( preserves-negatives-hom-Ab
        ( function-Ab G (Fin n))
        ( G)
        ( hom-sum-fin-sequence-type-Ab G n))
```

### Interchanging sums and subtraction

```agda
module _
  {l : Level}
  (G : Ab l)
  where

  abstract
    interchange-sum-right-subtraction-fin-sequence-type-Ab :
      (n : ℕ) (f g : fin-sequence-type-Ab G n) →
      sum-fin-sequence-type-Ab G n (λ i → right-subtraction-Ab G (f i) (g i)) ＝
      right-subtraction-Ab G
        ( sum-fin-sequence-type-Ab G n f)
        ( sum-fin-sequence-type-Ab G n g)
    interchange-sum-right-subtraction-fin-sequence-type-Ab n f g =
      ( interchange-sum-add-fin-sequence-type-Ab G n f (neg-Ab G ∘ g)) ∙
      ( ap-add-Ab G
        ( refl)
        ( inv (distributive-neg-sum-fin-sequence-type-Ab G n g)))
```

### Telescoping sums

A telescoping sum is a sum of the form `∑ aₙ₊₁ - aₙ` or `∑ aₙ - aₙ₊₁`.

```agda
module _
  {l : Level}
  (G : Ab l)
  where

  telescope-fin-sequence-type-Ab :
    (n : ℕ) → fin-sequence-type-Ab G (succ-ℕ n) → fin-sequence-type-Ab G n
  telescope-fin-sequence-type-Ab n u =
    ind-Σ (right-subtraction-Ab G) ∘ pair-succ-fin-sequence n u

  telescope-fin-sequence-type-Ab' :
    (n : ℕ) → fin-sequence-type-Ab G (succ-ℕ n) → fin-sequence-type-Ab G n
  telescope-fin-sequence-type-Ab' n u =
    ind-Σ (right-subtraction-Ab' G) ∘ pair-succ-fin-sequence n u

  abstract
    sum-telescope-fin-sequence-type-Ab :
      (n : ℕ) (u : fin-sequence-type-Ab G (succ-ℕ n)) →
      sum-fin-sequence-type-Ab G n (telescope-fin-sequence-type-Ab n u) ＝
      right-subtraction-Ab G (head-fin-sequence n u) (last-fin-sequence n u)
    sum-telescope-fin-sequence-type-Ab 0 u =
      inv (right-inverse-law-add-Ab G (head-fin-sequence 0 u))
    sum-telescope-fin-sequence-type-Ab (succ-ℕ n) u =
      ( ap-add-Ab G
        ( sum-telescope-fin-sequence-type-Ab n (tail-fin-sequence (succ-ℕ n) u))
        ( refl)) ∙
      ( commutative-add-Ab G _ _) ∙
      ( add-right-subtraction-Ab G _ _ _)

    sum-telescope-fin-sequence-type-Ab' :
      (n : ℕ) (u : fin-sequence-type-Ab G (succ-ℕ n)) →
      sum-fin-sequence-type-Ab G n (telescope-fin-sequence-type-Ab' n u) ＝
      right-subtraction-Ab G (last-fin-sequence n u) (head-fin-sequence n u)
    sum-telescope-fin-sequence-type-Ab' n u =
      ( htpy-sum-fin-sequence-type-Ab G
        ( n)
        ( λ i → inv (neg-right-subtraction-Ab G _ _))) ∙
      ( inv (distributive-neg-sum-fin-sequence-type-Ab G n _)) ∙
      ( ap (neg-Ab G) (sum-telescope-fin-sequence-type-Ab n u)) ∙
      ( neg-right-subtraction-Ab G _ _)
```

## See also

- [Sums of finite families of elements in abelian groups](group-theory.products-of-finite-families-of-elements-commutative-monoids.md)
