# Sums of finite sequences of elements in groups

```agda
module group-theory.sums-of-finite-sequences-of-elements-groups where
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
open import group-theory.sums-of-finite-sequences-of-elements-monoids

open import linear-algebra.finite-sequences-in-groups

open import univalent-combinatorics.coproduct-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The
{{#concept "sum operation" Disambiguation="of a finite sequence in a group" WD="sum" WDID=Q218005 Agda=sum-fin-sequence-type-Group}}
operation extends the binary operation on a [group](group-theory.groups.md) `G`
to any [finite sequence](lists.finite-sequences.md) of elements of `G`.

We use additive terminology consistently with the linear algebra definition of
[finite sequences in groups](linear-algebra.finite-sequences-in-groups.md)
despite the use of multiplicative terminology for groups in general.

## Definition

```agda
sum-fin-sequence-type-Group :
  {l : Level} (G : Group l) (n : ℕ) →
  (fin-sequence-type-Group G n) → type-Group G
sum-fin-sequence-type-Group G =
  sum-fin-sequence-type-Monoid (monoid-Group G)
```

## Properties

### Sums of one and two elements

```agda
module _
  {l : Level} (G : Group l)
  where

  compute-sum-one-element-Group :
    (f : fin-sequence-type-Group G 1) →
    sum-fin-sequence-type-Group G 1 f ＝ head-fin-sequence-type-Group G 0 f
  compute-sum-one-element-Group =
    compute-sum-one-element-Monoid (monoid-Group G)

  compute-sum-two-elements-Group :
    (f : fin-sequence-type-Group G 2) →
    sum-fin-sequence-type-Group G 2 f ＝
    mul-Group G (f (zero-Fin 1)) (f (one-Fin 1))
  compute-sum-two-elements-Group =
    compute-sum-two-elements-Monoid (monoid-Group G)
```

### Sums are homotopy invariant

```agda
module _
  {l : Level} (G : Group l)
  where

  htpy-sum-fin-sequence-type-Group :
    (n : ℕ) {f g : fin-sequence-type-Group G n} →
    (f ~ g) →
    sum-fin-sequence-type-Group G n f ＝ sum-fin-sequence-type-Group G n g
  htpy-sum-fin-sequence-type-Group =
    htpy-sum-fin-sequence-type-Monoid (monoid-Group G)
```

### Sums are equal to the zero-th term plus the rest

```agda
module _
  {l : Level} (G : Group l)
  where

  cons-sum-fin-sequence-type-Group :
    (n : ℕ) (f : fin-sequence-type-Group G (succ-ℕ n)) →
    {x : type-Group G} → head-fin-sequence-type-Group G n f ＝ x →
    sum-fin-sequence-type-Group G (succ-ℕ n) f ＝
    mul-Group G (sum-fin-sequence-type-Group G n (f ∘ inl-Fin n)) x
  cons-sum-fin-sequence-type-Group n f refl = refl

  snoc-sum-fin-sequence-type-Group :
    (n : ℕ) (f : fin-sequence-type-Group G (succ-ℕ n)) →
    {x : type-Group G} → f (zero-Fin n) ＝ x →
    sum-fin-sequence-type-Group G (succ-ℕ n) f ＝
    mul-Group G
      ( x)
      ( sum-fin-sequence-type-Group G n (f ∘ inr-Fin n))
  snoc-sum-fin-sequence-type-Group =
    snoc-sum-fin-sequence-type-Monoid (monoid-Group G)
```

### Extending a sum of elements in a group

```agda
module _
  {l : Level} (G : Group l)
  where

  extend-sum-fin-sequence-type-Group :
    (n : ℕ) (f : fin-sequence-type-Group G n) →
    sum-fin-sequence-type-Group G
      ( succ-ℕ n)
      ( cons-fin-sequence-type-Group G n (unit-Group G) f) ＝
    sum-fin-sequence-type-Group G n f
  extend-sum-fin-sequence-type-Group =
    extend-sum-fin-sequence-type-Monoid (monoid-Group G)
```

### Shifting a sum of elements in a group

```agda
module _
  {l : Level} (G : Group l)
  where

  shift-sum-fin-sequence-type-Group :
    (n : ℕ) (f : fin-sequence-type-Group G n) →
    sum-fin-sequence-type-Group G
      ( succ-ℕ n)
      ( snoc-fin-sequence-type-Group G n f
        ( unit-Group G)) ＝
    sum-fin-sequence-type-Group G n f
  shift-sum-fin-sequence-type-Group =
    shift-sum-fin-sequence-type-Monoid (monoid-Group G)
```

### A sum of zeros is zero

```agda
module _
  {l : Level} (G : Group l)
  where

  abstract
    sum-zero-fin-sequence-type-Group :
      (n : ℕ) →
      sum-fin-sequence-type-Group G n (zero-fin-sequence-type-Group G n) ＝
      unit-Group G
    sum-zero-fin-sequence-type-Group =
      sum-zero-fin-sequence-type-Monoid (monoid-Group G)
```

### Splitting sums of `n + m` elements into a sum of `n` elements and a sum of `m` elements

```agda
split-sum-fin-sequence-type-Group :
  {l : Level} (G : Group l)
  (n m : ℕ) (f : fin-sequence-type-Group G (n +ℕ m)) →
  sum-fin-sequence-type-Group G (n +ℕ m) f ＝
  mul-Group G
    ( sum-fin-sequence-type-Group G n (f ∘ inl-coproduct-Fin n m))
    ( sum-fin-sequence-type-Group G m (f ∘ inr-coproduct-Fin n m))
split-sum-fin-sequence-type-Group G =
  split-sum-fin-sequence-type-Monoid (monoid-Group G)
```

### Constant sums are the power operation

```agda
abstract
  sum-constant-fin-sequence-type-Group :
    {l : Level} (G : Group l) (n : ℕ) (x : type-Group G) →
    sum-fin-sequence-type-Group G n (λ _ → x) ＝ power-Group G n x
  sum-constant-fin-sequence-type-Group G =
    sum-constant-fin-sequence-type-Monoid (monoid-Group G)
```
