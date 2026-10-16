# Sums of finite sequences of elements of left modules over rings

```agda
module linear-algebra.sums-of-finite-sequences-of-elements-left-modules-rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import finite-group-theory.permutations-standard-finite-types

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.sums-of-finite-sequences-of-elements-abelian-groups

open import linear-algebra.function-left-modules-rings
open import linear-algebra.left-modules-rings
open import linear-algebra.linear-maps-left-modules-rings

open import lists.finite-sequences

open import ring-theory.rings

open import univalent-combinatorics.coproduct-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The
{{#concept "sum operation" Disambiguation="of a finite sequence in a left module over a ring" Agda=sum-fin-sequence-type-left-module-Ring}}
extends the binary addition operation on a
[left module](linear-algebra.left-modules-rings.md) `M` over a
[ring](ring-theory.rings.md) to any [finite sequence](lists.finite-sequences.md)
of elements of `M`.

## Definition

```agda
sum-fin-sequence-type-left-module-Ring :
  {l1 l2 : Level} (R : Ring l1) (M : left-module-Ring l2 R) →
  (n : ℕ) → fin-sequence (type-left-module-Ring R M) n →
  type-left-module-Ring R M
sum-fin-sequence-type-left-module-Ring R M =
  sum-fin-sequence-type-Ab (ab-left-module-Ring R M)
```

## Properties

### Sums of one and two elements

```agda
module _
  {l1 l2 : Level}
  (R : Ring l1)
  (M : left-module-Ring l2 R)
  where

  abstract
    compute-sum-one-element-left-module-Ring :
      (u : fin-sequence (type-left-module-Ring R M) 1) →
      sum-fin-sequence-type-left-module-Ring R M 1 u ＝
      head-fin-sequence 0 u
    compute-sum-one-element-left-module-Ring =
      compute-sum-one-element-Ab (ab-left-module-Ring R M)

    compute-sum-two-elements-left-module-Ring :
      (u : fin-sequence (type-left-module-Ring R M) 2) →
      sum-fin-sequence-type-left-module-Ring R M 2 u ＝
      add-left-module-Ring R M (u (zero-Fin 1)) (u (neg-one-Fin 1))
    compute-sum-two-elements-left-module-Ring =
      compute-sum-two-elements-Ab (ab-left-module-Ring R M)
```

### Sums are homotopy invariant

```agda
module _
  {l1 l2 : Level}
  (R : Ring l1)
  (M : left-module-Ring l2 R)
  where

  abstract
    htpy-sum-fin-sequence-type-left-module-Ring :
      (n : ℕ) {u v : fin-sequence (type-left-module-Ring R M) n} → u ~ v →
      sum-fin-sequence-type-left-module-Ring R M n u ＝
      sum-fin-sequence-type-left-module-Ring R M n v
    htpy-sum-fin-sequence-type-left-module-Ring =
      htpy-sum-fin-sequence-type-Ab (ab-left-module-Ring R M)
```

### The distributive law of scalar multiplication over sums

```agda
module _
  {l1 l2 : Level}
  (R : Ring l1)
  (M : left-module-Ring l2 R)
  where

  abstract
    left-distributive-mul-sum-fin-sequence-type-left-module-Ring :
      (n : ℕ)
      (r : type-Ring R) (u : fin-sequence (type-left-module-Ring R M) n) →
      mul-left-module-Ring R M
        ( r)
        ( sum-fin-sequence-type-left-module-Ring R M n u) ＝
      sum-fin-sequence-type-left-module-Ring R M
        ( n)
        ( mul-left-module-Ring R M r ∘ u)
    left-distributive-mul-sum-fin-sequence-type-left-module-Ring 0 r _ =
      right-zero-law-mul-left-module-Ring R M r
    left-distributive-mul-sum-fin-sequence-type-left-module-Ring
      (succ-ℕ n) r u =
      ( left-distributive-mul-add-left-module-Ring R M r _ _) ∙
      ( ap-add-left-module-Ring R M
        ( left-distributive-mul-sum-fin-sequence-type-left-module-Ring
          ( n)
          ( r)
          ( u ∘ inl-Fin n))
        ( refl))
```

### Splitting sums of `n + m` elements into a sum of `n` elements and a sum of `m` elements

```agda
module _
  {l1 l2 : Level}
  (R : Ring l1)
  (M : left-module-Ring l2 R)
  where

  abstract
    split-sum-fin-sequence-type-left-module-Ring :
      (n m : ℕ) (u : fin-sequence (type-left-module-Ring R M) (n +ℕ m)) →
      sum-fin-sequence-type-left-module-Ring R M (n +ℕ m) u ＝
      add-left-module-Ring R M
        ( sum-fin-sequence-type-left-module-Ring R M
          ( n)
          ( u ∘ inl-coproduct-Fin n m))
        ( sum-fin-sequence-type-left-module-Ring R M
          ( m)
          ( u ∘ inr-coproduct-Fin n m))
    split-sum-fin-sequence-type-left-module-Ring =
      split-sum-fin-sequence-type-Ab (ab-left-module-Ring R M)
```

### Permutations preserve sums

```agda
module _
  {l1 l2 : Level}
  (R : Ring l1)
  (M : left-module-Ring l2 R)
  where

  abstract
    preserves-sum-permutation-fin-sequence-type-left-module-Ring :
      (n : ℕ) (σ : Permutation n)
      (u : fin-sequence (type-left-module-Ring R M) n) →
      sum-fin-sequence-type-left-module-Ring R M n u ＝
      sum-fin-sequence-type-left-module-Ring R M n (u ∘ map-equiv σ)
    preserves-sum-permutation-fin-sequence-type-left-module-Ring =
      preserves-sum-permutation-fin-sequence-type-Ab
        ( ab-left-module-Ring R M)
```

### The distributive law of sums over addition

```agda
module _
  {l1 l2 : Level}
  (R : Ring l1)
  (M : left-module-Ring l2 R)
  where

  abstract
    interchange-sum-add-fin-sequence-type-left-module-Ring :
      (n : ℕ) (f g : fin-sequence (type-left-module-Ring R M) n) →
      sum-fin-sequence-type-left-module-Ring R M
        ( n)
        ( λ i → add-left-module-Ring R M (f i) (g i)) ＝
      add-left-module-Ring R M
        ( sum-fin-sequence-type-left-module-Ring R M n f)
        ( sum-fin-sequence-type-left-module-Ring R M n g)
    interchange-sum-add-fin-sequence-type-left-module-Ring =
      interchange-sum-add-fin-sequence-type-Ab (ab-left-module-Ring R M)
```

### The distributive law of negation over sums

```agda
module _
  {l1 l2 : Level}
  (R : Ring l1)
  (M : left-module-Ring l2 R)
  where

  abstract
    distributive-neg-sum-fin-sequence-type-left-module-Ring :
      (n : ℕ) (u : fin-sequence (type-left-module-Ring R M) n) →
      neg-left-module-Ring R M
        ( sum-fin-sequence-type-left-module-Ring R M n u) ＝
      sum-fin-sequence-type-left-module-Ring R M
        ( n)
        ( neg-left-module-Ring R M ∘ u)
    distributive-neg-sum-fin-sequence-type-left-module-Ring =
      distributive-neg-sum-fin-sequence-type-Ab (ab-left-module-Ring R M)
```

### Sums distribute over differences

```agda
module _
  {l1 l2 : Level}
  (R : Ring l1)
  (M : left-module-Ring l2 R)
  where

  abstract
    interchange-sum-diff-fin-sequence-type-left-module-Ring :
      (n : ℕ) (f g : fin-sequence (type-left-module-Ring R M) n) →
      sum-fin-sequence-type-left-module-Ring R M
        ( n)
        ( λ i → diff-left-module-Ring R M (f i) (g i)) ＝
      diff-left-module-Ring R M
        ( sum-fin-sequence-type-left-module-Ring R M n f)
        ( sum-fin-sequence-type-left-module-Ring R M n g)
    interchange-sum-diff-fin-sequence-type-left-module-Ring =
      interchange-sum-right-subtraction-fin-sequence-type-Ab
        ( ab-left-module-Ring R M)
```

### The sum operation is a linear map

```agda
module _
  {l1 l2 : Level}
  (R : Ring l1)
  (M : left-module-Ring l2 R)
  (n : ℕ)
  where

  abstract
    is-homogeneous-sum-fin-sequence-type-left-module-Ring :
      is-homogeneous-map-left-module-Ring
        ( R)
        ( function-left-module-Ring R M (Fin n))
        ( M)
        ( sum-fin-sequence-type-left-module-Ring R M n)
    is-homogeneous-sum-fin-sequence-type-left-module-Ring r u =
      inv
        ( left-distributive-mul-sum-fin-sequence-type-left-module-Ring
          ( R)
          ( M)
          ( n)
          ( r)
          ( u))

  is-linear-map-sum-fin-sequence-type-left-module-Ring :
    is-linear-map-left-module-Ring
      ( R)
      ( function-left-module-Ring R M (Fin n))
      ( M)
      ( sum-fin-sequence-type-left-module-Ring R M n)
  is-linear-map-sum-fin-sequence-type-left-module-Ring =
    ( interchange-sum-add-fin-sequence-type-left-module-Ring R M n ,
      is-homogeneous-sum-fin-sequence-type-left-module-Ring)

  linear-map-sum-fin-sequence-type-left-module-Ring :
    linear-map-left-module-Ring
      ( R)
      ( function-left-module-Ring R M (Fin n))
      ( M)
  linear-map-sum-fin-sequence-type-left-module-Ring =
    ( sum-fin-sequence-type-left-module-Ring R M n ,
      is-linear-map-sum-fin-sequence-type-left-module-Ring)
```
