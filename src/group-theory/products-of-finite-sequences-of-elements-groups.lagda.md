# Products of finite sequences of elements in groups

```agda
module group-theory.products-of-finite-sequences-of-elements-groups where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.unit-type
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import group-theory.groups
open import group-theory.powers-of-elements-groups
open import group-theory.products-of-finite-sequences-of-elements-monoids

open import linear-algebra.finite-sequences-in-groups

open import univalent-combinatorics.coproduct-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The
{{#concept "product operation" Disambiguation="of a finite sequence in a group" Agda=product-fin-sequence-type-Group}}
operation extends the binary operation on a [group](group-theory.groups.md) `G`
to any [finite sequence](lists.finite-sequences.md) of elements of `G`.

## Definition

```agda
product-fin-sequence-type-Group :
  {l : Level} (G : Group l) (n : ℕ) →
  (fin-sequence-type-Group G n) → type-Group G
product-fin-sequence-type-Group G =
  product-fin-sequence-type-Monoid (monoid-Group G)
```

## Properties

### Products of one and two elements

```agda
module _
  {l : Level} (G : Group l)
  where

  abstract
    compute-product-one-element-Group :
      (f : fin-sequence-type-Group G 1) →
      product-fin-sequence-type-Group G 1 f ＝
      head-fin-sequence-type-Group G 0 f
    compute-product-one-element-Group =
      compute-product-one-element-Monoid (monoid-Group G)

    compute-product-two-elements-Group :
      (f : fin-sequence-type-Group G 2) →
      product-fin-sequence-type-Group G 2 f ＝
      mul-Group G (f (zero-Fin 1)) (f (one-Fin 1))
    compute-product-two-elements-Group =
      compute-product-two-elements-Monoid (monoid-Group G)
```

### Products are homotopy invariant

```agda
module _
  {l : Level} (G : Group l)
  where

  abstract
    htpy-product-fin-sequence-type-Group :
      (n : ℕ) {f g : fin-sequence-type-Group G n} →
      (f ~ g) →
      product-fin-sequence-type-Group G n f ＝
      product-fin-sequence-type-Group G n g
    htpy-product-fin-sequence-type-Group =
      htpy-product-fin-sequence-type-Monoid (monoid-Group G)
```

### Products are equal to the zero-th term plus the rest

```agda
module _
  {l : Level} (G : Group l)
  where

  abstract
    cons-product-fin-sequence-type-Group :
      (n : ℕ) (f : fin-sequence-type-Group G (succ-ℕ n)) →
      product-fin-sequence-type-Group G (succ-ℕ n) f ＝
      mul-Group G
        ( product-fin-sequence-type-Group G n (f ∘ inl-Fin n))
        ( head-fin-sequence-type-Group G n f)
    cons-product-fin-sequence-type-Group n f = refl

    snoc-product-fin-sequence-type-Group :
      (n : ℕ) (f : fin-sequence-type-Group G (succ-ℕ n)) →
      product-fin-sequence-type-Group G (succ-ℕ n) f ＝
      mul-Group G
        ( f (zero-Fin n))
        ( product-fin-sequence-type-Group G n (f ∘ inr-Fin n))
    snoc-product-fin-sequence-type-Group =
      snoc-product-fin-sequence-type-Monoid (monoid-Group G)
```

### Extending a product of elements in a group

```agda
module _
  {l : Level} (G : Group l)
  where

  abstract
    extend-product-fin-sequence-type-Group :
      (n : ℕ) (f : fin-sequence-type-Group G n) →
      product-fin-sequence-type-Group G
        ( succ-ℕ n)
        ( cons-fin-sequence-type-Group G n (unit-Group G) f) ＝
      product-fin-sequence-type-Group G n f
    extend-product-fin-sequence-type-Group =
      extend-product-fin-sequence-type-Monoid (monoid-Group G)
```

### Shifting a product of elements in a group

```agda
module _
  {l : Level} (G : Group l)
  where

  abstract
    shift-product-fin-sequence-type-Group :
      (n : ℕ) (f : fin-sequence-type-Group G n) →
      product-fin-sequence-type-Group G
        ( succ-ℕ n)
        ( snoc-fin-sequence-type-Group G n f (unit-Group G)) ＝
      product-fin-sequence-type-Group G n f
    shift-product-fin-sequence-type-Group =
      shift-product-fin-sequence-type-Monoid (monoid-Group G)
```

### A product of units is the unit

```agda
module _
  {l : Level} (G : Group l)
  where

  abstract
    product-unit-fin-sequence-type-Group :
      (n : ℕ) →
      product-fin-sequence-type-Group G n (zero-fin-sequence-type-Group G n) ＝
      unit-Group G
    product-unit-fin-sequence-type-Group =
      product-unit-fin-sequence-type-Monoid (monoid-Group G)
```

### Splitting products of `n + m` elements into a product of `n` elements and a product of `m` elements

```agda
abstract
  split-product-fin-sequence-type-Group :
    {l : Level} (G : Group l)
    (n m : ℕ) (f : fin-sequence-type-Group G (n +ℕ m)) →
    product-fin-sequence-type-Group G (n +ℕ m) f ＝
    mul-Group G
      ( product-fin-sequence-type-Group G n (f ∘ inl-coproduct-Fin n m))
      ( product-fin-sequence-type-Group G m (f ∘ inr-coproduct-Fin n m))
  split-product-fin-sequence-type-Group G =
    split-product-fin-sequence-type-Monoid (monoid-Group G)
```

### Constant products are powers

```agda
abstract
  product-constant-fin-sequence-type-Group :
    {l : Level} (G : Group l) (n : ℕ) (x : type-Group G) →
    product-fin-sequence-type-Group G n (λ _ → x) ＝ power-Group G n x
  product-constant-fin-sequence-type-Group G =
    product-constant-fin-sequence-type-Monoid (monoid-Group G)
```
