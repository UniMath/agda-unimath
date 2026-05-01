# The dot product in standard Euclidean vector spaces

```agda
{-# OPTIONS --lossy-unification #-}

module linear-algebra.dot-product-standard-euclidean-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.universe-levels

open import linear-algebra.bilinear-forms-real-vector-spaces
open import linear-algebra.standard-euclidean-vector-spaces

open import order-theory.large-posets

open import real-numbers.absolute-value-real-numbers
open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.extensionality-multiplication-bilinear-form-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.square-roots-nonnegative-real-numbers
open import real-numbers.squares-real-numbers
open import real-numbers.sums-of-finite-sequences-of-nonnegative-real-numbers
open import real-numbers.sums-of-finite-sequences-of-real-numbers
open import real-numbers.zero-real-numbers

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The
{{#concept "dot product" WDID=Q181365 WD="scalar product" Disambiguation="of vectors in ℝⁿ" Agda=dot-product-ℝ-Fin}}
of two vectors `u` and `v` in
[`ℝⁿ`](linear-algebra.standard-euclidean-vector-spaces.md) is `∑ uᵢvᵢ`.

## Definition

```agda
dot-product-ℝ-Fin :
  {n : ℕ} {l : Level} → type-ℝ-Fin n l → type-ℝ-Fin n l → ℝ l
dot-product-ℝ-Fin {n} u v = sum-fin-sequence-ℝ n (λ i → u i *ℝ v i)
```

## Properties

### Symmetry of the dot product

```agda
abstract
  symmetric-dot-product-ℝ-Fin :
    {n : ℕ} {l : Level} (u v : type-ℝ-Fin n l) →
    dot-product-ℝ-Fin u v ＝ dot-product-ℝ-Fin v u
  symmetric-dot-product-ℝ-Fin {n} u v =
    htpy-sum-fin-sequence-ℝ n (λ i → commutative-mul-ℝ (u i) (v i))
```

### Distributivity laws

```agda
abstract
  left-distributive-dot-product-add-ℝ-Fin :
    {n : ℕ} {l : Level} (u v w : type-ℝ-Fin n l) →
    dot-product-ℝ-Fin u (add-ℝ-Fin v w) ＝
    dot-product-ℝ-Fin u v +ℝ dot-product-ℝ-Fin u w
  left-distributive-dot-product-add-ℝ-Fin {n} u v w =
    ( htpy-sum-fin-sequence-ℝ
      ( n)
      ( λ i → left-distributive-mul-add-ℝ (u i) (v i) (w i))) ∙
    ( inv (interchange-add-sum-fin-sequence-ℝ _ _ _))

  right-distributive-dot-product-add-ℝ-Fin :
    {n : ℕ} {l : Level} (u v w : type-ℝ-Fin n l) →
    dot-product-ℝ-Fin (add-ℝ-Fin u v) w ＝
    dot-product-ℝ-Fin u w +ℝ dot-product-ℝ-Fin v w
  right-distributive-dot-product-add-ℝ-Fin {n} u v w =
    ( htpy-sum-fin-sequence-ℝ
      ( n)
      ( λ i → right-distributive-mul-add-ℝ (u i) (v i) (w i))) ∙
    ( inv (interchange-add-sum-fin-sequence-ℝ _ _ _))
```

### Scalar multiplication laws

```agda
abstract
  preserves-left-scalar-mul-ℝ-Fin :
    {n : ℕ} {l : Level} (c : ℝ l) (u v : type-ℝ-Fin n l) →
    dot-product-ℝ-Fin (mul-ℝ-Fin c u) v ＝
    c *ℝ dot-product-ℝ-Fin u v
  preserves-left-scalar-mul-ℝ-Fin {n} c u v =
    ( htpy-sum-fin-sequence-ℝ n (λ i → associative-mul-ℝ c (u i) (v i))) ∙
    ( inv (left-distributive-mul-sum-fin-sequence-ℝ n c _))

  preserves-right-scalar-mul-ℝ-Fin :
    {n : ℕ} {l : Level} (c : ℝ l) (u v : type-ℝ-Fin n l) →
    dot-product-ℝ-Fin u (mul-ℝ-Fin c v) ＝
    c *ℝ dot-product-ℝ-Fin u v
  preserves-right-scalar-mul-ℝ-Fin {n} c u v =
    ( htpy-sum-fin-sequence-ℝ n (λ i → left-swap-mul-ℝ (u i) c (v i))) ∙
    ( inv (left-distributive-mul-sum-fin-sequence-ℝ n c _))
```

### The dot product is a bilinear form

```agda
bilinear-form-dot-product-ℝ-Fin :
  (n : ℕ) (l : Level) →
  bilinear-form-ℝ-Vector-Space (vector-space-ℝ-Fin n l)
bilinear-form-dot-product-ℝ-Fin n l =
  ( dot-product-ℝ-Fin ,
    right-distributive-dot-product-add-ℝ-Fin ,
    preserves-left-scalar-mul-ℝ-Fin ,
    left-distributive-dot-product-add-ℝ-Fin ,
    preserves-right-scalar-mul-ℝ-Fin)
```

### `v · v` is nonnegative

```agda
abstract
  is-nonnegative-diagonal-dot-product-ℝ-Fin :
    {n : ℕ} {l : Level} (v : type-ℝ-Fin n l) →
    is-nonnegative-ℝ (dot-product-ℝ-Fin v v)
  is-nonnegative-diagonal-dot-product-ℝ-Fin {n} v =
    is-nonnegative-real-sum-fin-sequence-ℝ⁰⁺
      ( n)
      ( λ i → nonnegative-square-ℝ (v i))

nonnegative-diagonal-dot-product-ℝ-Fin :
  {n : ℕ} {l : Level} (v : type-ℝ-Fin n l) → ℝ⁰⁺ l
nonnegative-diagonal-dot-product-ℝ-Fin v =
  ( dot-product-ℝ-Fin v v ,
    is-nonnegative-diagonal-dot-product-ℝ-Fin v)
```

### If `v · v = 0`, `v` is the zero vector

```agda
abstract
  htpy-zero-is-zero-diagonal-dot-product-ℝ-Fin :
    {n : ℕ} {l : Level} (v : type-ℝ-Fin n l) →
    is-zero-ℝ (dot-product-ℝ-Fin v v) →
    (i : Fin n) → v i ＝ raise-zero-ℝ l
  htpy-zero-is-zero-diagonal-dot-product-ℝ-Fin {n} v v·v=0 i =
    eq-raise-zero-is-zero-ℝ
      ( is-zero-is-zero-square-ℝ
        ( is-all-zero-is-zero-sum-fin-sequence-ℝ⁰⁺
          ( n)
          ( λ i → nonnegative-square-ℝ (v i))
          ( v·v=0)
          ( i)))

  extensionality-dot-product-ℝ-Fin :
    {n : ℕ} {l : Level} (v : type-ℝ-Fin n l) →
    is-zero-ℝ (dot-product-ℝ-Fin v v) → v ＝ zero-ℝ-Fin n l
  extensionality-dot-product-ℝ-Fin v v·v=0 =
    eq-htpy (htpy-zero-is-zero-diagonal-dot-product-ℝ-Fin v v·v=0)
```

### If every coordinate of `v : ℝⁿ` has absolute value at most `ε`, `v · v ≤ nε²`

```agda
abstract
  leq-mul-dimension-bound-dot-product-ℝ-Fin :
    (n : ℕ) {l1 l2 : Level} (v : type-ℝ-Fin n l1) (ε : ℝ⁰⁺ l2) →
    ((i : Fin n) → leq-ℝ (abs-ℝ (v i)) (real-ℝ⁰⁺ ε)) →
    leq-ℝ (dot-product-ℝ-Fin v v) (real-ℕ n *ℝ square-ℝ (real-ℝ⁰⁺ ε))
  leq-mul-dimension-bound-dot-product-ℝ-Fin n v ε |vᵢ|≤ε =
    let open inequality-reasoning-Large-Poset ℝ-Large-Poset
    in
      chain-of-inequalities
      real-sum-fin-sequence-ℝ⁰⁺ n (λ i → nonnegative-square-ℝ (v i))
      ≤ real-sum-fin-sequence-ℝ⁰⁺ n (λ i → nonnegative-square-ℝ (abs-ℝ (v i)))
        by
          leq-eq-ℝ
            ( htpy-sum-fin-sequence-ℝ n (λ i → (inv (square-abs-ℝ (v i)))))
      ≤ real-sum-fin-sequence-ℝ⁰⁺ n (λ i → nonnegative-square-ℝ (real-ℝ⁰⁺ ε))
        by
          preserves-leq-sum-fin-sequence-ℝ⁰⁺ n _ _
            ( λ i →
              preserves-leq-square-ℝ⁰⁺
                ( nonnegative-abs-ℝ (v i))
                ( ε)
                ( |vᵢ|≤ε i))
      ≤ real-ℕ n *ℝ square-ℝ (real-ℝ⁰⁺ ε)
        by leq-eq-ℝ (sum-constant-fin-sequence-ℝ n (square-ℝ (real-ℝ⁰⁺ ε)))
```

### The square of every coordinate of `v` is at most `v · v`

```agda
abstract
  leq-square-diagonal-dot-product-ℝ-Fin :
    {n : ℕ} {l : Level} (v : type-ℝ-Fin n l) (i : Fin n) →
    leq-ℝ (square-ℝ (v i)) (dot-product-ℝ-Fin v v)
  leq-square-diagonal-dot-product-ℝ-Fin {n} v =
    leq-term-sum-fin-sequence-ℝ⁰⁺ n (λ i → nonnegative-square-ℝ (v i))
```

### The absolute value of every coordinate of $v$ is at most $\sqrt{v · v}$

```agda
abstract
  leq-abs-sqrt-diagonal-dot-product-ℝ-Fin :
    {n : ℕ} {l : Level} (v : type-ℝ-Fin n l) (i : Fin n) →
    leq-ℝ
      ( abs-ℝ (v i))
      ( real-sqrt-ℝ⁰⁺ (nonnegative-diagonal-dot-product-ℝ-Fin v))
  leq-abs-sqrt-diagonal-dot-product-ℝ-Fin {n} v i =
    binary-tr
      ( leq-ℝ)
      ( inv (eq-abs-sqrt-square-ℝ (v i)))
      ( refl)
      ( preserves-leq-sqrt-ℝ⁰⁺
        ( nonnegative-square-ℝ (v i))
        ( nonnegative-diagonal-dot-product-ℝ-Fin v)
        ( leq-square-diagonal-dot-product-ℝ-Fin v i))
```

## See also

- [The standard Euclidean inner product spaces](linear-algebra.standard-euclidean-inner-product-spaces.md)

## External links

- [Dot product](https://en.wikipedia.org/wiki/Dot_product) on Wikipedia
