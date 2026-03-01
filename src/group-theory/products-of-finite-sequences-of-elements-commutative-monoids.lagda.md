# Products of finite sequences of elements in commutative monoids

```agda
{-# OPTIONS --lossy-unification #-}

module group-theory.products-of-finite-sequences-of-elements-commutative-monoids where
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
open import group-theory.powers-of-elements-commutative-monoids
open import group-theory.products-of-finite-sequences-of-elements-commutative-semigroups
open import group-theory.products-of-finite-sequences-of-elements-monoids

open import linear-algebra.finite-sequences-in-commutative-monoids

open import univalent-combinatorics.coproduct-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The
{{#concept "product operation" Disambiguation="of a finite sequence in a commutative monoid" Agda=product-fin-sequence-type-Commutative-Monoid}}
extends the binary operation on a
[commutative monoid](group-theory.commutative-monoids.md) `M` to any
[finite sequence](lists.finite-sequences.md) of elements of `M`.

## Definition

```agda
product-fin-sequence-type-Commutative-Monoid :
  {l : Level} (M : Commutative-Monoid l) (n : ℕ) →
  fin-sequence-type-Commutative-Monoid M n → type-Commutative-Monoid M
product-fin-sequence-type-Commutative-Monoid M =
  product-fin-sequence-type-Monoid (monoid-Commutative-Monoid M)
```

## Properties

#### Nontrivial products in a commutative monoid equal products in the underlying commutative semigroup

```agda
module _
  {l : Level} (M : Commutative-Monoid l)
  where

  abstract
    eq-product-commutative-semigroup-product-fin-sequence-type-Commutative-Monoid :
      (n : ℕ) (f : fin-sequence-type-Commutative-Monoid M (succ-ℕ n)) →
      product-fin-sequence-type-Commutative-Monoid M (succ-ℕ n) f ＝
      product-fin-sequence-type-Commutative-Semigroup
        ( commutative-semigroup-Commutative-Monoid M)
        ( n)
        ( f)
    eq-product-commutative-semigroup-product-fin-sequence-type-Commutative-Monoid
      zero-ℕ f = left-unit-law-mul-Commutative-Monoid M _
    eq-product-commutative-semigroup-product-fin-sequence-type-Commutative-Monoid
      (succ-ℕ n) f =
      ap
        ( mul-Commutative-Monoid' M _)
        ( eq-product-commutative-semigroup-product-fin-sequence-type-Commutative-Monoid
          ( n)
          ( f ∘ inl))
```

### Products of one and two elements

```agda
module _
  {l : Level} (M : Commutative-Monoid l)
  where

  abstract
    compute-product-one-element-Commutative-Monoid :
      (f : fin-sequence-type-Commutative-Monoid M 1) →
      product-fin-sequence-type-Commutative-Monoid M 1 f ＝
      head-fin-sequence-type-Commutative-Monoid M 0 f
    compute-product-one-element-Commutative-Monoid =
      compute-product-one-element-Monoid (monoid-Commutative-Monoid M)

    compute-product-two-elements-Commutative-Monoid :
      (f : fin-sequence-type-Commutative-Monoid M 2) →
      product-fin-sequence-type-Commutative-Monoid M 2 f ＝
      mul-Commutative-Monoid M (f (zero-Fin 1)) (f (one-Fin 1))
    compute-product-two-elements-Commutative-Monoid =
      compute-product-two-elements-Monoid (monoid-Commutative-Monoid M)
```

### Products are homotopy invariant

```agda
module _
  {l : Level} (M : Commutative-Monoid l)
  where

  abstract
    htpy-product-fin-sequence-type-Commutative-Monoid :
      (n : ℕ) {f g : fin-sequence-type-Commutative-Monoid M n} →
      (f ~ g) →
      product-fin-sequence-type-Commutative-Monoid M n f ＝
      product-fin-sequence-type-Commutative-Monoid M n g
    htpy-product-fin-sequence-type-Commutative-Monoid =
      htpy-product-fin-sequence-type-Monoid (monoid-Commutative-Monoid M)
```

### Products are equal to the zero-th term plus the rest

```agda
module _
  {l : Level} (M : Commutative-Monoid l)
  where

  abstract
    cons-product-fin-sequence-type-Commutative-Monoid :
      (n : ℕ) (f : fin-sequence-type-Commutative-Monoid M (succ-ℕ n)) →
      product-fin-sequence-type-Commutative-Monoid M (succ-ℕ n) f ＝
      mul-Commutative-Monoid M
        ( product-fin-sequence-type-Commutative-Monoid M n (f ∘ inl-Fin n))
        ( head-fin-sequence-type-Commutative-Monoid M n f)
    cons-product-fin-sequence-type-Commutative-Monoid =
      cons-product-fin-sequence-type-Monoid (monoid-Commutative-Monoid M)

    snoc-product-fin-sequence-type-Commutative-Monoid :
      (n : ℕ) (f : fin-sequence-type-Commutative-Monoid M (succ-ℕ n)) →
      product-fin-sequence-type-Commutative-Monoid M (succ-ℕ n) f ＝
      mul-Commutative-Monoid M
        ( f (zero-Fin n))
        ( product-fin-sequence-type-Commutative-Monoid M n (f ∘ inr-Fin n))
    snoc-product-fin-sequence-type-Commutative-Monoid =
      snoc-product-fin-sequence-type-Monoid (monoid-Commutative-Monoid M)
```

### Extending a product of elements in a monoid

```agda
module _
  {l : Level} (M : Commutative-Monoid l)
  where

  abstract
    extend-product-fin-sequence-type-Commutative-Monoid :
      (n : ℕ) (f : fin-sequence-type-Commutative-Monoid M n) →
      product-fin-sequence-type-Commutative-Monoid M
        ( succ-ℕ n)
        ( cons-fin-sequence-type-Commutative-Monoid
          ( M)
          ( n)
          ( unit-Commutative-Monoid M)
          ( f)) ＝
      product-fin-sequence-type-Commutative-Monoid M n f
    extend-product-fin-sequence-type-Commutative-Monoid =
      extend-product-fin-sequence-type-Monoid (monoid-Commutative-Monoid M)
```

### Shifting a product of elements in a monoid

```agda
module _
  {l : Level} (M : Commutative-Monoid l)
  where

  abstract
    shift-product-fin-sequence-type-Commutative-Monoid :
      (n : ℕ) (f : fin-sequence-type-Commutative-Monoid M n) →
      product-fin-sequence-type-Commutative-Monoid M
        ( succ-ℕ n)
        ( snoc-fin-sequence-type-Commutative-Monoid M n f
          ( unit-Commutative-Monoid M)) ＝
      product-fin-sequence-type-Commutative-Monoid M n f
    shift-product-fin-sequence-type-Commutative-Monoid =
      shift-product-fin-sequence-type-Monoid (monoid-Commutative-Monoid M)
```

### A product of units is the unit

```agda
module _
  {l : Level} (M : Commutative-Monoid l)
  where

  abstract
    product-unit-fin-sequence-type-Commutative-Monoid :
      (n : ℕ) →
      product-fin-sequence-type-Commutative-Monoid
        ( M)
        ( n)
        ( zero-fin-sequence-type-Commutative-Monoid M n) ＝
      unit-Commutative-Monoid M
    product-unit-fin-sequence-type-Commutative-Monoid =
      product-unit-fin-sequence-type-Monoid (monoid-Commutative-Monoid M)
```

### Splitting products of `n + m` elements into a product of `n` elements and a product of `m` elements

```agda
abstract
  split-product-fin-sequence-type-Commutative-Monoid :
    {l : Level} (M : Commutative-Monoid l)
    (n m : ℕ) (f : fin-sequence-type-Commutative-Monoid M (n +ℕ m)) →
    product-fin-sequence-type-Commutative-Monoid M (n +ℕ m) f ＝
    mul-Commutative-Monoid M
      ( product-fin-sequence-type-Commutative-Monoid
        ( M)
        ( n)
        ( f ∘ inl-coproduct-Fin n m))
      ( product-fin-sequence-type-Commutative-Monoid
        ( M)
        ( m)
        ( f ∘ inr-coproduct-Fin n m))
  split-product-fin-sequence-type-Commutative-Monoid M =
    split-product-fin-sequence-type-Monoid (monoid-Commutative-Monoid M)
```

### Permutations preserve products

```agda
module _
  {l : Level} (M : Commutative-Monoid l)
  where

  abstract
    preserves-product-permutation-fin-sequence-type-Commutative-Monoid :
      (n : ℕ) (σ : Permutation n) →
      (f : fin-sequence-type-Commutative-Monoid M n) →
      product-fin-sequence-type-Commutative-Monoid M n f ＝
      product-fin-sequence-type-Commutative-Monoid M n (f ∘ map-equiv σ)
    preserves-product-permutation-fin-sequence-type-Commutative-Monoid
      zero-ℕ _ f = refl
    preserves-product-permutation-fin-sequence-type-Commutative-Monoid
      (succ-ℕ n) σ f =
      ( eq-product-commutative-semigroup-product-fin-sequence-type-Commutative-Monoid
        ( M)
        ( n)
        ( f)) ∙
      ( preserves-product-permutation-fin-sequence-type-Commutative-Semigroup
        ( commutative-semigroup-Commutative-Monoid M)
        ( n)
        ( σ)
        ( f)) ∙
      ( inv
        ( eq-product-commutative-semigroup-product-fin-sequence-type-Commutative-Monoid
          ( M)
          ( n)
          ( f ∘ map-equiv σ)))
```

### Constant products are powers

```agda
abstract
  product-constant-fin-sequence-type-Commutative-Monoid :
    {l : Level} (M : Commutative-Monoid l) (n : ℕ) →
    (x : type-Commutative-Monoid M) →
    product-fin-sequence-type-Commutative-Monoid M n (λ _ → x) ＝
    power-Commutative-Monoid M n x
  product-constant-fin-sequence-type-Commutative-Monoid M =
    product-constant-fin-sequence-type-Monoid (monoid-Commutative-Monoid M)
```

## See also

- [Products of finite families of elements in commutative monoids](group-theory.products-of-finite-families-of-elements-commutative-monoids.md)
