# Sums of finite sequences in semirings

```agda
module ring-theory.sums-of-finite-sequences-of-elements-semirings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import finite-group-theory.permutations-standard-finite-types

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.unit-type
open import foundation.universe-levels

open import group-theory.products-of-finite-sequences-of-elements-commutative-monoids

open import linear-algebra.finite-sequences-in-semirings

open import lists.finite-sequences

open import ring-theory.multiples-of-elements-semirings
open import ring-theory.semirings

open import univalent-combinatorics.coproduct-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The
{{#concept "sum operation" Disambiguation="over finite sequences in a semiring" WD="sum" WDID=Q218005 Agda=sum-fin-sequence-type-Semiring}}
extends the binary addition operation on a [semiring](ring-theory.semirings.md)
`R` to any [finite sequence](lists.finite-sequences.md) of elements of `R`.

## Definition

```agda
sum-fin-sequence-type-Semiring :
  {l : Level} (R : Semiring l) (n : ℕ) →
  (fin-sequence-type-Semiring R n) → type-Semiring R
sum-fin-sequence-type-Semiring R =
  product-fin-sequence-type-Commutative-Monoid
    ( additive-commutative-monoid-Semiring R)
```

## Properties

### Sums of one and two elements

```agda
module _
  {l : Level} (R : Semiring l)
  where

  compute-sum-one-element-Semiring :
    (f : fin-sequence-type-Semiring R 1) →
    sum-fin-sequence-type-Semiring R 1 f ＝ head-fin-sequence 0 f
  compute-sum-one-element-Semiring =
    compute-product-one-element-Commutative-Monoid
      ( additive-commutative-monoid-Semiring R)

  compute-sum-two-elements-Semiring :
    (f : fin-sequence-type-Semiring R 2) →
    sum-fin-sequence-type-Semiring R 2 f ＝
    add-Semiring R (f (zero-Fin 1)) (f (one-Fin 1))
  compute-sum-two-elements-Semiring =
    compute-product-two-elements-Commutative-Monoid
      ( additive-commutative-monoid-Semiring R)
```

### Sums are homotopy invariant

```agda
module _
  {l : Level} (R : Semiring l)
  where

  abstract
    htpy-sum-fin-sequence-type-Semiring :
      (n : ℕ) {f g : fin-sequence-type-Semiring R n} →
      (f ~ g) →
      sum-fin-sequence-type-Semiring R n f ＝
      sum-fin-sequence-type-Semiring R n g
    htpy-sum-fin-sequence-type-Semiring =
      htpy-product-fin-sequence-type-Commutative-Monoid
        ( additive-commutative-monoid-Semiring R)
```

### Sums are equal to the zero-th term plus the rest

```agda
module _
  {l : Level} (R : Semiring l)
  where

  abstract
    cons-sum-fin-sequence-type-Semiring :
      (n : ℕ) (f : fin-sequence-type-Semiring R (succ-ℕ n)) →
      sum-fin-sequence-type-Semiring R (succ-ℕ n) f ＝
      add-Semiring R
        ( sum-fin-sequence-type-Semiring R n (f ∘ inl-Fin n))
        ( head-fin-sequence n f)
    cons-sum-fin-sequence-type-Semiring n f = refl

    snoc-sum-fin-sequence-type-Semiring :
      (n : ℕ) (f : fin-sequence-type-Semiring R (succ-ℕ n)) →
      sum-fin-sequence-type-Semiring R (succ-ℕ n) f ＝
      add-Semiring R
        ( f (zero-Fin n))
        ( sum-fin-sequence-type-Semiring R n (f ∘ inr-Fin n))
    snoc-sum-fin-sequence-type-Semiring =
      snoc-product-fin-sequence-type-Commutative-Monoid
        ( additive-commutative-monoid-Semiring R)
```

### Multiplication distributes over sums

```agda
module _
  {l : Level} (R : Semiring l)
  where

  abstract
    left-distributive-mul-sum-fin-sequence-type-Semiring :
      (n : ℕ) (x : type-Semiring R)
      (f : fin-sequence-type-Semiring R n) →
      mul-Semiring R x (sum-fin-sequence-type-Semiring R n f) ＝
      sum-fin-sequence-type-Semiring R n (λ i → mul-Semiring R x (f i))
    left-distributive-mul-sum-fin-sequence-type-Semiring zero-ℕ x f =
      right-zero-law-mul-Semiring R x
    left-distributive-mul-sum-fin-sequence-type-Semiring (succ-ℕ n) x f =
      ( left-distributive-mul-add-Semiring R x
        ( sum-fin-sequence-type-Semiring R n (f ∘ inl-Fin n))
        ( f (inr star))) ∙
      ( ap
        ( add-Semiring' R (mul-Semiring R x (f (inr star))))
        ( left-distributive-mul-sum-fin-sequence-type-Semiring
          ( n)
          ( x)
          ( f ∘ inl-Fin n)))

    right-distributive-mul-sum-fin-sequence-type-Semiring :
      (n : ℕ) (f : fin-sequence-type-Semiring R n)
      (x : type-Semiring R) →
      mul-Semiring R (sum-fin-sequence-type-Semiring R n f) x ＝
      sum-fin-sequence-type-Semiring R n (λ i → mul-Semiring R (f i) x)
    right-distributive-mul-sum-fin-sequence-type-Semiring zero-ℕ f x =
      left-zero-law-mul-Semiring R x
    right-distributive-mul-sum-fin-sequence-type-Semiring (succ-ℕ n) f x =
      ( right-distributive-mul-add-Semiring R
        ( sum-fin-sequence-type-Semiring R n (f ∘ inl-Fin n))
        ( f (inr star))
        ( x)) ∙
      ( ap
        ( add-Semiring' R (mul-Semiring R (f (inr star)) x))
        ( right-distributive-mul-sum-fin-sequence-type-Semiring
          ( n)
          ( f ∘ inl-Fin n)
          ( x)))
```

### Interchange law of sums and addition in a semiring

```agda
module _
  {l : Level} (R : Semiring l)
  where

  abstract
    interchange-add-sum-fin-sequence-type-Semiring :
      (n : ℕ) (f g : fin-sequence-type-Semiring R n) →
      add-Semiring R
        ( sum-fin-sequence-type-Semiring R n f)
        ( sum-fin-sequence-type-Semiring R n g) ＝
      sum-fin-sequence-type-Semiring R n
        ( add-fin-sequence-type-Semiring R n f g)
    interchange-add-sum-fin-sequence-type-Semiring zero-ℕ f g =
      left-unit-law-add-Semiring R (zero-Semiring R)
    interchange-add-sum-fin-sequence-type-Semiring (succ-ℕ n) f g =
      ( interchange-add-add-Semiring R
        ( sum-fin-sequence-type-Semiring R n (f ∘ inl-Fin n))
        ( f (neg-one-Fin n))
        ( sum-fin-sequence-type-Semiring R n (g ∘ inl-Fin n))
        ( g (neg-one-Fin n))) ∙
      ( ap
        ( add-Semiring' R
          ( add-Semiring R (f (inr star)) (g (inr star))))
        ( interchange-add-sum-fin-sequence-type-Semiring n
          ( f ∘ inl-Fin n)
          ( g ∘ inl-Fin n)))
```

### Extending a sum of elements in a semiring

```agda
module _
  {l : Level} (R : Semiring l)
  where

  abstract
    extend-sum-fin-sequence-type-Semiring :
      (n : ℕ) (f : fin-sequence-type-Semiring R n) →
      sum-fin-sequence-type-Semiring R
        ( succ-ℕ n)
        ( cons-fin-sequence-type-Semiring R n (zero-Semiring R) f) ＝
      sum-fin-sequence-type-Semiring R n f
    extend-sum-fin-sequence-type-Semiring =
      extend-product-fin-sequence-type-Commutative-Monoid
        ( additive-commutative-monoid-Semiring R)
```

### Shifting a sum of elements in a semiring

```agda
module _
  {l : Level} (R : Semiring l)
  where

  abstract
    shift-sum-fin-sequence-type-Semiring :
      (n : ℕ) (f : fin-sequence-type-Semiring R n) →
      sum-fin-sequence-type-Semiring R
        ( succ-ℕ n)
        ( snoc-fin-sequence-type-Semiring R n f (zero-Semiring R)) ＝
      sum-fin-sequence-type-Semiring R n f
    shift-sum-fin-sequence-type-Semiring =
      shift-product-fin-sequence-type-Commutative-Monoid
        ( additive-commutative-monoid-Semiring R)
```

### A sum of zeroes is zero

```agda
module _
  {l : Level} (R : Semiring l)
  where

  abstract
    sum-zero-fin-sequence-type-Semiring :
      (n : ℕ) →
      sum-fin-sequence-type-Semiring
        ( R)
        ( n)
        ( zero-fin-sequence-type-Semiring R n) ＝
      zero-Semiring R
    sum-zero-fin-sequence-type-Semiring =
      product-unit-fin-sequence-type-Commutative-Monoid
        ( additive-commutative-monoid-Semiring R)
```

### Splitting sums of `n + m` elements into a sum of `n` elements and a sum of `m` elements

```agda
abstract
  split-sum-fin-sequence-type-Semiring :
    {l : Level} (R : Semiring l)
    (n m : ℕ) (f : fin-sequence-type-Semiring R (n +ℕ m)) →
    sum-fin-sequence-type-Semiring R (n +ℕ m) f ＝
    add-Semiring R
      ( sum-fin-sequence-type-Semiring R n (f ∘ inl-coproduct-Fin n m))
      ( sum-fin-sequence-type-Semiring R m (f ∘ inr-coproduct-Fin n m))
  split-sum-fin-sequence-type-Semiring R =
    split-product-fin-sequence-type-Commutative-Monoid
      ( additive-commutative-monoid-Semiring R)
```

### Permutations preserve sums

```agda
module _
  {l : Level} (R : Semiring l)
  where

  abstract
    preserves-sum-permutation-fin-sequence-type-Semiring :
      (n : ℕ) → (σ : Permutation n) →
      (f : fin-sequence-type-Semiring R n) →
      sum-fin-sequence-type-Semiring R n f ＝
      sum-fin-sequence-type-Semiring R n (f ∘ map-equiv σ)
    preserves-sum-permutation-fin-sequence-type-Semiring =
      preserves-product-permutation-fin-sequence-type-Commutative-Monoid
        ( additive-commutative-monoid-Semiring R)
```

### The sum of a constant finite sequence in a semiring is scalar multiplication by the length of the sequence

```agda
abstract
  sum-constant-fin-sequence-type-Semiring :
    {l : Level} (R : Semiring l) (n : ℕ) (x : type-Semiring R) →
    sum-fin-sequence-type-Semiring R n (λ _ → x) ＝
    multiple-Semiring R n x
  sum-constant-fin-sequence-type-Semiring R =
    product-constant-fin-sequence-type-Commutative-Monoid
      ( additive-commutative-monoid-Semiring R)
```

## See also

- [Sums of finite families of elements in semirings](ring-theory.sums-of-finite-families-of-elements-semirings.md)
