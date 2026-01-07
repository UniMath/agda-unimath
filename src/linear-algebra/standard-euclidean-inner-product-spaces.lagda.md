# The standard Euclidean inner product spaces

```agda
{-# OPTIONS --lossy-unification #-}

module linear-algebra.standard-euclidean-inner-product-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.multiplication-positive-rational-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.universe-levels

open import linear-algebra.dot-product-standard-euclidean-vector-spaces
open import linear-algebra.normed-real-vector-spaces
open import linear-algebra.real-inner-product-spaces
open import linear-algebra.real-inner-product-spaces-are-normed
open import linear-algebra.standard-euclidean-vector-spaces

open import metric-spaces.lipschitz-functions-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.metrics
open import metric-spaces.rational-neighborhood-relations
open import metric-spaces.short-functions-metric-spaces
open import metric-spaces.uniform-homeomorphisms-metric-spaces
open import metric-spaces.uniformly-continuous-functions-metric-spaces

open import order-theory.large-posets

open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.distance-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.metric-space-of-functions-into-real-numbers
open import real-numbers.multiplication-nonnegative-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.positive-and-negative-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.square-roots-nonnegative-real-numbers
open import real-numbers.squares-real-numbers
open import real-numbers.strict-inequality-real-numbers
open import real-numbers.zero-real-numbers

open import univalent-combinatorics.standard-finite-types
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

normed-vector-space-ℝ^ : ℕ → (l : Level) → Normed-ℝ-Vector-Space l (lsuc l)
normed-vector-space-ℝ^ n l =
  normed-vector-space-ℝ-Inner-Product-Space (inner-product-space-ℝ^ n l)

squared-euclidean-norm-ℝ^ : (n : ℕ) {l : Level} → type-ℝ^ n l → ℝ l
squared-euclidean-norm-ℝ^ n {l} =
  squared-norm-ℝ-Inner-Product-Space (inner-product-space-ℝ^ n l)

euclidean-norm-ℝ^ : (n : ℕ) {l : Level} → type-ℝ^ n l → ℝ l
euclidean-norm-ℝ^ n {l} =
  norm-ℝ-Inner-Product-Space (inner-product-space-ℝ^ n l)

nonnegative-euclidean-norm-ℝ^ : (n : ℕ) {l : Level} → type-ℝ^ n l → ℝ⁰⁺ l
nonnegative-euclidean-norm-ℝ^ n {l} =
  nonnegative-norm-Normed-ℝ-Vector-Space (normed-vector-space-ℝ^ n l)

euclidean-dist-ℝ^ : (n : ℕ) {l : Level} → type-ℝ^ n l → type-ℝ^ n l → ℝ l
euclidean-dist-ℝ^ n u v =
  euclidean-norm-ℝ^ n (diff-ℝ^ n u v)

nonnegative-euclidean-dist-ℝ^ :
  (n : ℕ) {l : Level} → type-ℝ^ n l → type-ℝ^ n l → ℝ⁰⁺ l
nonnegative-euclidean-dist-ℝ^ n u v =
  nonnegative-euclidean-norm-ℝ^ n (diff-ℝ^ n u v)

abstract
  triangular-euclidean-norm-ℝ^ :
    (n : ℕ) {l : Level} (u v : type-ℝ^ n l) →
    leq-ℝ
      ( euclidean-norm-ℝ^ n (add-ℝ^ n u v))
      ( euclidean-norm-ℝ^ n u +ℝ euclidean-norm-ℝ^ n v)
  triangular-euclidean-norm-ℝ^ n {l} =
    triangular-norm-Normed-ℝ-Vector-Space (normed-vector-space-ℝ^ n l)

  triangular-euclidean-dist-ℝ^ :
    (n : ℕ) {l : Level} (u v w : type-ℝ^ n l) →
    leq-ℝ
      ( euclidean-dist-ℝ^ n u w)
      ( euclidean-dist-ℝ^ n u v +ℝ euclidean-dist-ℝ^ n v w)
  triangular-euclidean-dist-ℝ^ n {l} =
    triangular-dist-Normed-ℝ-Vector-Space (normed-vector-space-ℝ^ n l)

  is-extensional-euclidean-norm-ℝ^ :
    (n : ℕ) {l : Level} (v : type-ℝ^ n l) →
    is-zero-ℝ (euclidean-norm-ℝ^ n v) → v ＝ zero-ℝ^ n l
  is-extensional-euclidean-norm-ℝ^ n {l} =
    is-extensional-norm-Normed-ℝ-Vector-Space (normed-vector-space-ℝ^ n l)

  is-metric-euclidean-dist-ℝ^ :
    (n : ℕ) (l : Level) →
    is-metric-distance-function
      ( set-ℝ^ n l)
      ( nonnegative-euclidean-dist-ℝ^ n)
  is-metric-euclidean-dist-ℝ^ n l =
    is-metric-dist-Normed-ℝ-Vector-Space (normed-vector-space-ℝ^ n l)

euclidean-metric-space-ℝ^ : ℕ → (l : Level) → Metric-Space (lsuc l) l
euclidean-metric-space-ℝ^ n l =
  metric-space-ℝ-Inner-Product-Space (inner-product-space-ℝ^ n l)

euclidean-neighborhood-prop-ℝ^ :
  (n : ℕ) (l : Level) → Rational-Neighborhood-Relation l (type-ℝ^ n l)
euclidean-neighborhood-prop-ℝ^ n l =
  neighborhood-prop-Metric-Space (euclidean-metric-space-ℝ^ n l)

euclidean-neighborhood-ℝ^ :
  (n : ℕ) (l : Level) → ℚ⁺ → Relation l (type-ℝ^ n l)
euclidean-neighborhood-ℝ^ n l =
  neighborhood-Metric-Space (euclidean-metric-space-ℝ^ n l)
```

## Properties

### The identity is a short map from the Euclidean metric space over `ℝⁿ` to the product metric space over `ℝⁿ`

```agda
abstract
  is-short-map-id-euclidean-product-metric-space-ℝ^ :
    (n : ℕ) (l : Level) →
    is-short-function-Metric-Space
      ( euclidean-metric-space-ℝ^ n l)
      ( function-into-ℝ-Metric-Space (Fin n) l)
      ( id)
  is-short-map-id-euclidean-product-metric-space-ℝ^ n l ε u v ∥u-v∥≤ε i =
    neighborhood-dist-ℝ
      ( ε)
      ( u i)
      ( v i)
      ( transitive-leq-ℝ
        ( dist-ℝ (u i) (v i))
        ( euclidean-norm-ℝ^ n (diff-ℝ^ n u v))
        ( real-ℚ⁺ ε)
        ( ∥u-v∥≤ε)
        ( leq-abs-sqrt-diagonal-dot-product-ℝ^ n (diff-ℝ^ n u v) i))

  is-uniformly-continuous-map-id-euclidean-product-metric-space-ℝ^ :
    (n : ℕ) (l : Level) →
    is-uniformly-continuous-function-Metric-Space
      ( euclidean-metric-space-ℝ^ n l)
      ( function-into-ℝ-Metric-Space (Fin n) l)
      ( id)
  is-uniformly-continuous-map-id-euclidean-product-metric-space-ℝ^ n l =
    is-uniformly-continuous-is-short-function-Metric-Space
      ( euclidean-metric-space-ℝ^ n l)
      ( function-into-ℝ-Metric-Space (Fin n) l)
      ( id)
      ( is-short-map-id-euclidean-product-metric-space-ℝ^ n l)
```

### The identity is a Lipschitz map from the product metric space `ℝⁿ` to the Euclidean metric space over `ℝⁿ`

```agda
abstract
  is-lipschitz-constant-map-id-product-euclidean-metric-space-ℝ^ :
    (n : ℕ) (l : Level) (α : ℚ⁺) →
    leq-ℝ (real-sqrt-ℝ⁰⁺ (nonnegative-real-ℕ n)) (real-ℚ⁺ α) →
    is-lipschitz-constant-function-Metric-Space
      ( function-into-ℝ-Metric-Space (Fin n) l)
      ( euclidean-metric-space-ℝ^ n l)
      ( id)
      ( α)
  is-lipschitz-constant-map-id-product-euclidean-metric-space-ℝ^
    n l α √n≤α ε u v Nεuv =
    let
      open inequality-reasoning-Large-Poset ℝ-Large-Poset
    in
      chain-of-inequalities
      euclidean-norm-ℝ^ n (diff-ℝ^ n u v)
      ≤ real-sqrt-ℝ⁰⁺
          ( nonnegative-real-ℕ n *ℝ⁰⁺ nonnegative-square-ℝ (real-ℚ⁺ ε))
        by
          preserves-leq-sqrt-ℝ⁰⁺
            ( nonnegative-diagonal-dot-product-ℝ^ n (diff-ℝ^ n u v))
            ( nonnegative-real-ℕ n *ℝ⁰⁺ nonnegative-square-ℝ (real-ℚ⁺ ε))
            ( leq-mul-dimension-bound-dot-product-ℝ^
              ( n)
              ( diff-ℝ^ n u v)
              ( nonnegative-real-ℚ⁺ ε)
              ( λ i →
                leq-dist-neighborhood-ℝ
                  ( ε)
                  ( u i)
                  ( v i)
                  ( Nεuv i)))
      ≤ ( real-sqrt-ℝ⁰⁺ (nonnegative-real-ℕ n)) *ℝ
        ( real-sqrt-ℝ⁰⁺ (nonnegative-square-ℝ (real-ℚ⁺ ε)))
        by leq-eq-ℝ (ap real-ℝ⁰⁺ (distributive-sqrt-mul-ℝ⁰⁺ _ _))
      ≤ real-ℚ⁺ α *ℝ real-ℚ⁺ ε
        by
          preserves-leq-mul-ℝ⁰⁺
            ( sqrt-ℝ⁰⁺ (nonnegative-real-ℕ n))
            ( nonnegative-real-ℚ⁺ α)
            ( sqrt-ℝ⁰⁺ (nonnegative-square-ℝ (real-ℚ⁺ ε)))
            ( nonnegative-real-ℚ⁺ ε)
            ( √n≤α)
            ( leq-eq-ℝ
              ( ap real-ℝ⁰⁺ (is-retraction-square-ℝ⁰⁺ (nonnegative-real-ℚ⁺ ε))))
      ≤ real-ℚ⁺ (α *ℚ⁺ ε)
        by leq-eq-ℝ (mul-real-ℚ _ _)

  is-lipschitz-map-id-product-euclidean-metric-space-ℝ^ :
    (n : ℕ) (l : Level) →
    is-lipschitz-function-Metric-Space
      ( function-into-ℝ-Metric-Space (Fin n) l)
      ( euclidean-metric-space-ℝ^ n l)
      ( id)
  is-lipschitz-map-id-product-euclidean-metric-space-ℝ^ n l =
    let
      open
        do-syntax-trunc-Prop
          ( is-lipschitz-function-prop-Metric-Space
            ( function-into-ℝ-Metric-Space (Fin n) l)
            ( euclidean-metric-space-ℝ^ n l)
            ( id))
    in do
      (α , √n<α) ← le-some-rational-ℝ (real-sqrt-ℝ⁰⁺ (nonnegative-real-ℕ n))
      let
        α⁺ =
          ( α ,
            reflects-is-positive-real-ℚ
              ( is-positive-le-ℝ⁰⁺
                ( sqrt-ℝ⁰⁺ (nonnegative-real-ℕ n))
                ( real-ℚ α)
                ( √n<α)))
      intro-exists
        ( α⁺)
        ( is-lipschitz-constant-map-id-product-euclidean-metric-space-ℝ^
          ( n)
          ( l)
          ( α⁺)
          ( leq-le-ℝ √n<α))

  is-uniformly-continuous-map-id-product-euclidean-metric-space-ℝ^ :
    (n : ℕ) (l : Level) →
    is-uniformly-continuous-function-Metric-Space
      ( function-into-ℝ-Metric-Space (Fin n) l)
      ( euclidean-metric-space-ℝ^ n l)
      ( id)
  is-uniformly-continuous-map-id-product-euclidean-metric-space-ℝ^ n l =
    is-uniformly-continuous-is-lipschitz-function-Metric-Space
      ( function-into-ℝ-Metric-Space (Fin n) l)
      ( euclidean-metric-space-ℝ^ n l)
      ( id)
      ( is-lipschitz-map-id-product-euclidean-metric-space-ℝ^ n l)
```

### The identity is a uniform homeomorphism between the product metric space `ℝⁿ` and the Euclidean metric space `ℝⁿ`

```agda
uniform-homeomorphism-id-product-euclidean-metric-space-ℝ^ :
  (n : ℕ) (l : Level) →
  uniform-homeomorphism-Metric-Space
    ( function-into-ℝ-Metric-Space (Fin n) l)
    ( euclidean-metric-space-ℝ^ n l)
uniform-homeomorphism-id-product-euclidean-metric-space-ℝ^ n l =
  ( id ,
    is-equiv-id ,
    is-uniformly-continuous-map-id-product-euclidean-metric-space-ℝ^ n l ,
    is-uniformly-continuous-map-id-euclidean-product-metric-space-ℝ^ n l)
```
