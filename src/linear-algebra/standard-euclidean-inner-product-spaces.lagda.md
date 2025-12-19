# The standard Euclidean inner product spaces

```agda
module linear-algebra.standard-euclidean-inner-product-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.universe-levels

open import linear-algebra.dot-product-standard-euclidean-vector-spaces
open import linear-algebra.real-inner-product-spaces
open import linear-algebra.standard-euclidean-vector-spaces
```

</details>

## Idea

The standard Euclidean
[inner product space](linear-algebra.real-inner-product-spaces.md) is the
[standard Euclidean vector space](linear-algebra.standard-euclidean-vector-spaces.md),
with inner product the
[dot product](linear-algebra.dot-product-standard-euclidean-vector-spaces.md).

## Definition

```agda
inner-product-space-ℝ^ : ℕ → (l : Level) → ℝ-Inner-Product-Space l (lsuc l)
inner-product-space-ℝ^ n l =
  ( vector-space-ℝ^ n l ,
    bilinear-form-dot-product-ℝ^ n l ,
    symmetric-dot-product-ℝ^ n ,
    is-nonnegative-diagonal-dot-product-ℝ^ n ,
    extensionality-dot-product-ℝ^ n)
```
