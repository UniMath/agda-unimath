# The dot product in standard Euclidean vector spaces

```agda
{-# OPTIONS --lossy-unification #-}

module linear-algebra.dot-product-standard-euclidean-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import linear-algebra.standard-euclidean-vector-spaces
open import foundation.universe-levels
open import linear-algebra.bilinear-forms-real-vector-spaces
open import real-numbers.addition-real-numbers
open import foundation.identity-types
open import real-numbers.nonnegative-real-numbers
open import foundation.dependent-pair-types
open import real-numbers.squares-real-numbers
open import elementary-number-theory.natural-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.sums-of-finite-sequences-of-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.sums-of-finite-sequences-of-nonnegative-real-numbers
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

## Definition

```agda
dot-product-ℝ^ : (n : ℕ) {l : Level} → type-ℝ^ n l → type-ℝ^ n l → ℝ l
dot-product-ℝ^ n u v = sum-fin-sequence-ℝ n (λ i → u i *ℝ v i)
```

## Properties

### Symmetry of the dot product

```agda
abstract
  symmetric-dot-product-ℝ^ :
    (n : ℕ) {l : Level} (u v : type-ℝ^ n l) →
    dot-product-ℝ^ n u v ＝ dot-product-ℝ^ n v u
  symmetric-dot-product-ℝ^ n u v =
    htpy-sum-fin-sequence-ℝ n (λ i → commutative-mul-ℝ (u i) (v i))
```

### Distributivity laws

```agda
abstract
  left-distributive-dot-product-add-ℝ^ :
    (n : ℕ) {l : Level} (u v w : type-ℝ^ n l) →
    dot-product-ℝ^ n u (add-ℝ^ n v w) ＝
    dot-product-ℝ^ n u v +ℝ dot-product-ℝ^ n u w
  left-distributive-dot-product-add-ℝ^ n u v w =
    ( htpy-sum-fin-sequence-ℝ
      ( n)
      ( λ i → left-distributive-mul-add-ℝ (u i) (v i) (w i))) ∙
    ( inv (interchange-add-sum-fin-sequence-ℝ _ _ _))

  right-distributive-dot-product-add-ℝ^ :
    (n : ℕ) {l : Level} (u v w : type-ℝ^ n l) →
    dot-product-ℝ^ n (add-ℝ^ n u v) w ＝
    dot-product-ℝ^ n u w +ℝ dot-product-ℝ^ n v w
  right-distributive-dot-product-add-ℝ^ n u v w =
    ( htpy-sum-fin-sequence-ℝ
      ( n)
      ( λ i → right-distributive-mul-add-ℝ (u i) (v i) (w i))) ∙
    ( inv (interchange-add-sum-fin-sequence-ℝ _ _ _))
```

### Scalar multiplication laws

```agda
abstract
  preserves-left-scalar-mul-ℝ^ :
    (n : ℕ) {l : Level} (c : ℝ l) (u v : type-ℝ^ n l) →
    dot-product-ℝ^ n (mul-ℝ^ n c u) v ＝ c *ℝ dot-product-ℝ^ n u v
  preserves-left-scalar-mul-ℝ^ n c u v =
    ( htpy-sum-fin-sequence-ℝ n (λ i → associative-mul-ℝ c (u i) (v i))) ∙
    ( inv (left-distributive-mul-sum-fin-sequence-ℝ n c _))

  preserves-right-scalar-mul-ℝ^ :
    (n : ℕ) {l : Level} (c : ℝ l) (u v : type-ℝ^ n l) →
    dot-product-ℝ^ n u (mul-ℝ^ n c v) ＝ c *ℝ dot-product-ℝ^ n u v
  preserves-right-scalar-mul-ℝ^ n c u v =
    ( htpy-sum-fin-sequence-ℝ n (λ i → left-swap-mul-ℝ (u i) c (v i))) ∙
    ( inv (left-distributive-mul-sum-fin-sequence-ℝ n c _))
```

### The dot product is a bilinear form

```agda
bilinear-form-dot-product-ℝ^ :
  (n : ℕ) (l : Level) → bilinear-form-ℝ-Vector-Space (vector-space-ℝ^ n l)
bilinear-form-dot-product-ℝ^ n l =
  ( dot-product-ℝ^ n ,
    right-distributive-dot-product-add-ℝ^ n ,
    preserves-left-scalar-mul-ℝ^ n ,
    left-distributive-dot-product-add-ℝ^ n ,
    preserves-right-scalar-mul-ℝ^ n)
```

### `v · v` is nonnegative

```agda
abstract
  is-nonnegative-diagonal-dot-product-ℝ^ :
    (n : ℕ) {l : Level} (v : type-ℝ^ n l) →
    is-nonnegative-ℝ (dot-product-ℝ^ n v v)
  is-nonnegative-diagonal-dot-product-ℝ^ n v =
    is-nonnegative-real-sum-fin-sequence-ℝ⁰⁺
      ( n)
      ( λ i → nonnegative-square-ℝ (v i))
```
