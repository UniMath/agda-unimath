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
{{#concept "dot product" WDID=Q181365 WD="scalar product" Disambiguation="of vectors in ℝⁿ" Agda=dot-product-ℝ^}}
of two vectors `u` and `v` in
[`ℝⁿ`](linear-algebra.standard-euclidean-vector-spaces.md) is `∑ uᵢvᵢ`.

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

nonnegative-diagonal-dot-product-ℝ^ :
  (n : ℕ) {l : Level} (v : type-ℝ^ n l) → ℝ⁰⁺ l
nonnegative-diagonal-dot-product-ℝ^ n v =
  ( dot-product-ℝ^ n v v ,
    is-nonnegative-diagonal-dot-product-ℝ^ n v)
```

### If `v · v = 0`, `v` is the zero vector

```agda
abstract
  htpy-zero-is-zero-diagonal-dot-product-ℝ^ :
    (n : ℕ) {l : Level} (v : type-ℝ^ n l) →
    is-zero-ℝ (dot-product-ℝ^ n v v) →
    (i : Fin n) → v i ＝ raise-zero-ℝ l
  htpy-zero-is-zero-diagonal-dot-product-ℝ^ n v v·v=0 i =
    eq-zero-eq-zero-square-ℝ
      ( v i)
      ( ap
        ( real-ℝ⁰⁺)
        ( is-all-zero-eq-zero-sum-fin-sequence-ℝ⁰⁺
          ( n)
          ( λ i → nonnegative-square-ℝ (v i))
          ( eq-ℝ⁰⁺ _ _ (eq-raise-zero-is-zero-ℝ (v·v=0)))
          ( i)))

  extensionality-dot-product-ℝ^ :
    (n : ℕ) {l : Level} (v : type-ℝ^ n l) →
    is-zero-ℝ (dot-product-ℝ^ n v v) → v ＝ zero-ℝ^ n l
  extensionality-dot-product-ℝ^ n v v·v=0 =
    eq-htpy (htpy-zero-is-zero-diagonal-dot-product-ℝ^ n v v·v=0)
```

### If every coordinate of `v : ℝⁿ` has absolute value at most `ε`, `v · v ≤ nε²`

```agda
abstract
  leq-mul-dimension-bound-dot-product-ℝ^ :
    (n : ℕ) {l1 l2 : Level} (v : type-ℝ^ n l1) (ε : ℝ⁰⁺ l2) →
    ((i : Fin n) → leq-ℝ (abs-ℝ (v i)) (real-ℝ⁰⁺ ε)) →
    leq-ℝ (dot-product-ℝ^ n v v) (real-ℕ n *ℝ square-ℝ (real-ℝ⁰⁺ ε))
  leq-mul-dimension-bound-dot-product-ℝ^ n v ε |vᵢ|≤ε =
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
  leq-square-diagonal-dot-product-ℝ^ :
    (n : ℕ) {l : Level} (v : type-ℝ^ n l) (i : Fin n) →
    leq-ℝ (square-ℝ (v i)) (dot-product-ℝ^ n v v)
  leq-square-diagonal-dot-product-ℝ^ n v =
    leq-term-sum-fin-sequence-ℝ⁰⁺ n (λ i → nonnegative-square-ℝ (v i))
```

### The absolute value of every coordinate of $v$ is at most $\sqrt{v · v}$

```agda
abstract
  leq-abs-sqrt-diagonal-dot-product :
    (n : ℕ) {l : Level} (v : type-ℝ^ n l) (i : Fin n) →
    leq-ℝ
      ( abs-ℝ (v i))
      ( real-sqrt-ℝ⁰⁺ (nonnegative-diagonal-dot-product-ℝ^ n v))
  leq-abs-sqrt-diagonal-dot-product n v i =
    binary-tr
      ( leq-ℝ)
      ( inv (eq-abs-sqrt-square-ℝ (v i)))
      ( refl)
      ( preserves-leq-sqrt-ℝ⁰⁺
        ( nonnegative-square-ℝ (v i))
        ( nonnegative-diagonal-dot-product-ℝ^ n v)
        ( leq-square-diagonal-dot-product-ℝ^ n v i))
```

## See also

- [The standard Euclidean inner product spaces](linear-algebra.standard-euclidean-inner-product-spaces.md)

## External links

- [Dot product](https://en.wikipedia.org/wiki/Dot_product) on Wikipedia
