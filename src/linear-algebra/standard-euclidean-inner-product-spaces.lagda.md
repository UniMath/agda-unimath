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

open import metric-spaces.lipschitz-maps-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.metrics
open import metric-spaces.rational-neighborhood-relations
open import metric-spaces.short-maps-metric-spaces
open import metric-spaces.uniform-homeomorphisms-metric-spaces
open import metric-spaces.uniformly-continuous-maps-metric-spaces

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
inner-product-space-fin-sequence-ℝ :
  ℕ → (l : Level) → ℝ-Inner-Product-Space l (lsuc l)
inner-product-space-fin-sequence-ℝ n l =
  ( vector-space-fin-sequence-ℝ n l ,
    bilinear-form-dot-product-fin-sequence-ℝ n l ,
    symmetric-dot-product-fin-sequence-ℝ ,
    is-nonnegative-diagonal-dot-product-fin-sequence-ℝ ,
    extensionality-dot-product-fin-sequence-ℝ)

normed-vector-space-fin-sequence-ℝ :
  ℕ → (l : Level) → Normed-ℝ-Vector-Space l (lsuc l)
normed-vector-space-fin-sequence-ℝ n l =
  normed-vector-space-ℝ-Inner-Product-Space
    ( inner-product-space-fin-sequence-ℝ n l)

squared-euclidean-norm-fin-sequence-ℝ :
  {n : ℕ} {l : Level} → type-fin-sequence-ℝ n l → ℝ l
squared-euclidean-norm-fin-sequence-ℝ {n} {l} =
  squared-norm-ℝ-Inner-Product-Space (inner-product-space-fin-sequence-ℝ n l)

euclidean-norm-fin-sequence-ℝ :
  {n : ℕ} {l : Level} → type-fin-sequence-ℝ n l → ℝ l
euclidean-norm-fin-sequence-ℝ {n} {l} =
  norm-ℝ-Inner-Product-Space (inner-product-space-fin-sequence-ℝ n l)

nonnegative-euclidean-norm-fin-sequence-ℝ :
  {n : ℕ} {l : Level} → type-fin-sequence-ℝ n l → ℝ⁰⁺ l
nonnegative-euclidean-norm-fin-sequence-ℝ {n} {l} =
  nonnegative-norm-Normed-ℝ-Vector-Space
    ( normed-vector-space-fin-sequence-ℝ n l)

euclidean-dist-fin-sequence-ℝ :
  {n : ℕ} {l : Level} → type-fin-sequence-ℝ n l → type-fin-sequence-ℝ n l → ℝ l
euclidean-dist-fin-sequence-ℝ {n} u v =
  euclidean-norm-fin-sequence-ℝ (diff-fin-sequence-ℝ u v)

nonnegative-euclidean-dist-fin-sequence-ℝ :
  {n : ℕ} {l : Level} →
  type-fin-sequence-ℝ n l → type-fin-sequence-ℝ n l → ℝ⁰⁺ l
nonnegative-euclidean-dist-fin-sequence-ℝ u v =
  nonnegative-euclidean-norm-fin-sequence-ℝ (diff-fin-sequence-ℝ u v)

abstract
  triangular-euclidean-norm-fin-sequence-ℝ :
    (n : ℕ) {l : Level} (u v : type-fin-sequence-ℝ n l) →
    leq-ℝ
      ( euclidean-norm-fin-sequence-ℝ (add-fin-sequence-ℝ u v))
      ( euclidean-norm-fin-sequence-ℝ u +ℝ euclidean-norm-fin-sequence-ℝ v)
  triangular-euclidean-norm-fin-sequence-ℝ n {l} =
    triangular-norm-Normed-ℝ-Vector-Space
      ( normed-vector-space-fin-sequence-ℝ n l)

  triangular-euclidean-dist-fin-sequence-ℝ :
    (n : ℕ) {l : Level} (u v w : type-fin-sequence-ℝ n l) →
    leq-ℝ
      ( euclidean-dist-fin-sequence-ℝ u w)
      ( ( euclidean-dist-fin-sequence-ℝ u v) +ℝ
        ( euclidean-dist-fin-sequence-ℝ v w))
  triangular-euclidean-dist-fin-sequence-ℝ n {l} =
    triangular-dist-Normed-ℝ-Vector-Space
      ( normed-vector-space-fin-sequence-ℝ n l)

  is-extensional-euclidean-norm-fin-sequence-ℝ :
    (n : ℕ) {l : Level} (v : type-fin-sequence-ℝ n l) →
    is-zero-ℝ (euclidean-norm-fin-sequence-ℝ v) → v ＝ zero-fin-sequence-ℝ n l
  is-extensional-euclidean-norm-fin-sequence-ℝ n {l} =
    is-extensional-norm-Normed-ℝ-Vector-Space
      ( normed-vector-space-fin-sequence-ℝ n l)

  is-metric-euclidean-dist-fin-sequence-ℝ :
    (n : ℕ) (l : Level) →
    is-metric-distance-function
      ( set-fin-sequence-ℝ n l)
      ( nonnegative-euclidean-dist-fin-sequence-ℝ)
  is-metric-euclidean-dist-fin-sequence-ℝ n l =
    is-metric-dist-Normed-ℝ-Vector-Space
      ( normed-vector-space-fin-sequence-ℝ n l)

euclidean-metric-space-fin-sequence-ℝ :
  ℕ → (l : Level) → Metric-Space (lsuc l) l
euclidean-metric-space-fin-sequence-ℝ n l =
  metric-space-ℝ-Inner-Product-Space (inner-product-space-fin-sequence-ℝ n l)

euclidean-neighborhood-prop-fin-sequence-ℝ :
  (n : ℕ) (l : Level) →
  Rational-Neighborhood-Relation l (type-fin-sequence-ℝ n l)
euclidean-neighborhood-prop-fin-sequence-ℝ n l =
  neighborhood-prop-Metric-Space (euclidean-metric-space-fin-sequence-ℝ n l)

euclidean-neighborhood-fin-sequence-ℝ :
  (n : ℕ) (l : Level) → ℚ⁺ → Relation l (type-fin-sequence-ℝ n l)
euclidean-neighborhood-fin-sequence-ℝ n l =
  neighborhood-Metric-Space (euclidean-metric-space-fin-sequence-ℝ n l)
```

## Properties

### The identity is a short map from the Euclidean metric space over `ℝⁿ` to the product metric space over `ℝⁿ`

```agda
abstract
  is-short-map-id-euclidean-product-metric-space-fin-sequence-ℝ :
    (n : ℕ) (l : Level) →
    is-short-map-Metric-Space
      ( euclidean-metric-space-fin-sequence-ℝ n l)
      ( function-into-ℝ-Metric-Space (Fin n) l)
      ( id)
  is-short-map-id-euclidean-product-metric-space-fin-sequence-ℝ
    n l ε u v ∥u-v∥≤ε i =
    neighborhood-dist-ℝ
      ( ε)
      ( u i)
      ( v i)
      ( transitive-leq-ℝ
        ( dist-ℝ (u i) (v i))
        ( euclidean-norm-fin-sequence-ℝ (diff-fin-sequence-ℝ u v))
        ( real-ℚ⁺ ε)
        ( ∥u-v∥≤ε)
        ( leq-abs-sqrt-diagonal-dot-product-fin-sequence-ℝ
          ( diff-fin-sequence-ℝ u v)
          ( i)))

  is-uniformly-continuous-map-id-euclidean-product-metric-space-fin-sequence-ℝ :
    (n : ℕ) (l : Level) →
    is-uniformly-continuous-map-Metric-Space
      ( euclidean-metric-space-fin-sequence-ℝ n l)
      ( function-into-ℝ-Metric-Space (Fin n) l)
      ( id)
  is-uniformly-continuous-map-id-euclidean-product-metric-space-fin-sequence-ℝ
    n l =
    is-uniformly-continuous-map-is-short-map-Metric-Space
      ( euclidean-metric-space-fin-sequence-ℝ n l)
      ( function-into-ℝ-Metric-Space (Fin n) l)
      ( id)
      ( is-short-map-id-euclidean-product-metric-space-fin-sequence-ℝ n l)
```

### The identity is a Lipschitz map from the product metric space `ℝⁿ` to the Euclidean metric space over `ℝⁿ`

```agda
abstract
  is-lipschitz-constant-map-id-product-euclidean-metric-space-fin-sequence-ℝ :
    (n : ℕ) (l : Level) (α : ℚ⁺) →
    leq-ℝ (real-sqrt-ℝ⁰⁺ (nonnegative-real-ℕ n)) (real-ℚ⁺ α) →
    is-lipschitz-constant-map-Metric-Space
      ( function-into-ℝ-Metric-Space (Fin n) l)
      ( euclidean-metric-space-fin-sequence-ℝ n l)
      ( id)
      ( α)
  is-lipschitz-constant-map-id-product-euclidean-metric-space-fin-sequence-ℝ
    n l α √n≤α ε u v Nεuv =
    let
      open inequality-reasoning-Large-Poset ℝ-Large-Poset
    in
      chain-of-inequalities
      euclidean-norm-fin-sequence-ℝ (diff-fin-sequence-ℝ u v)
      ≤ real-sqrt-ℝ⁰⁺
          ( nonnegative-real-ℕ n *ℝ⁰⁺ nonnegative-square-ℝ (real-ℚ⁺ ε))
        by
          preserves-leq-sqrt-ℝ⁰⁺
            ( nonnegative-diagonal-dot-product-fin-sequence-ℝ
              ( diff-fin-sequence-ℝ u v))
            ( nonnegative-real-ℕ n *ℝ⁰⁺ nonnegative-square-ℝ (real-ℚ⁺ ε))
            ( leq-mul-dimension-bound-dot-product-fin-sequence-ℝ
              ( n)
              ( diff-fin-sequence-ℝ u v)
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

  is-lipschitz-map-id-product-euclidean-metric-space-fin-sequence-ℝ :
    (n : ℕ) (l : Level) →
    is-lipschitz-map-Metric-Space
      ( function-into-ℝ-Metric-Space (Fin n) l)
      ( euclidean-metric-space-fin-sequence-ℝ n l)
      ( id)
  is-lipschitz-map-id-product-euclidean-metric-space-fin-sequence-ℝ n l =
    let
      open
        do-syntax-trunc-Prop
          ( is-lipschitz-prop-map-Metric-Space
            ( function-into-ℝ-Metric-Space (Fin n) l)
            ( euclidean-metric-space-fin-sequence-ℝ n l)
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
        ( is-lipschitz-constant-map-id-product-euclidean-metric-space-fin-sequence-ℝ
          ( n)
          ( l)
          ( α⁺)
          ( leq-le-ℝ √n<α))

  is-uniformly-continuous-map-id-product-euclidean-metric-space-fin-sequence-ℝ :
    (n : ℕ) (l : Level) →
    is-uniformly-continuous-map-Metric-Space
      ( function-into-ℝ-Metric-Space (Fin n) l)
      ( euclidean-metric-space-fin-sequence-ℝ n l)
      ( id)
  is-uniformly-continuous-map-id-product-euclidean-metric-space-fin-sequence-ℝ
    n l =
    is-uniformly-continuous-map-is-lipschitz-map-Metric-Space
      ( function-into-ℝ-Metric-Space (Fin n) l)
      ( euclidean-metric-space-fin-sequence-ℝ n l)
      ( id)
      ( is-lipschitz-map-id-product-euclidean-metric-space-fin-sequence-ℝ n l)
```

### The identity is a uniform homeomorphism between the product metric space `ℝⁿ` and the Euclidean metric space `ℝⁿ`

```agda
uniform-homeomorphism-id-product-euclidean-metric-space-fin-sequence-ℝ :
  (n : ℕ) (l : Level) →
  uniform-homeomorphism-Metric-Space
    ( function-into-ℝ-Metric-Space (Fin n) l)
    ( euclidean-metric-space-fin-sequence-ℝ n l)
uniform-homeomorphism-id-product-euclidean-metric-space-fin-sequence-ℝ n l =
  ( id ,
    is-equiv-id ,
    is-uniformly-continuous-map-id-product-euclidean-metric-space-fin-sequence-ℝ
      ( n)
      ( l) ,
    is-uniformly-continuous-map-id-euclidean-product-metric-space-fin-sequence-ℝ
      ( n)
      ( l))
```
