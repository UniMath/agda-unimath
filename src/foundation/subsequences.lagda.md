# Subsequences

```agda
module foundation.subsequences where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers

open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.sequences
open import foundation.universe-levels

open import order-theory.infinite-limit-sequences-preorders
open import order-theory.strict-order-preserving-maps
open import order-theory.strictly-increasing-sequences-strictly-preordered-sets
```

</details>

## Idea

A {{concept "subsequence" Agda=subsequence}} of a
[sequence](foundation.sequences.md) `u : ℕ → A` is a sequence `u ∘ f` for some
[strictly increasing](order-theory.strict-order-preserving-maps.md) sequence
`f : ℕ → ℕ`.

## Definitions

### Subsequences of a sequence

```agda
module _
  {l : Level} {A : UU l} (u : sequence A)
  where

  subsequence : UU lzero
  subsequence =
    hom-Strictly-Preordered-Set
      strictly-preordered-set-ℕ
      strictly-preordered-set-ℕ

  extract-subsequence : subsequence → ℕ → ℕ
  extract-subsequence =
    map-hom-Strictly-Preordered-Set
      strictly-preordered-set-ℕ
      strictly-preordered-set-ℕ

  is-strictly-increasing-extract-subsequence :
    (f : subsequence) →
    preserves-strict-order-map-Strictly-Preordered-Set
      ( strictly-preordered-set-ℕ)
      ( strictly-preordered-set-ℕ)
      ( extract-subsequence f)
  is-strictly-increasing-extract-subsequence =
    preserves-strict-order-hom-Strictly-Preordered-Set
      strictly-preordered-set-ℕ
      strictly-preordered-set-ℕ

  seq-subsequence : subsequence → sequence A
  seq-subsequence f n = u (extract-subsequence f n)
```

## Properties

### Any sequence is a subsequence of itself

```agda
module _
  {l : Level} {A : UU l} (u : sequence A)
  where

  refl-subsequence : subsequence u
  refl-subsequence = id-hom-Strictly-Preordered-Set strictly-preordered-set-ℕ
```

### A subsequence of a subsequence is a subsequence of the original sequence

```agda
module _
  {l : Level} {A : UU l} (u : sequence A)
  where

  sub-subsequence :
    (v : subsequence u) →
    (w : subsequence (seq-subsequence u v)) →
    subsequence u
  sub-subsequence =
    comp-hom-Strictly-Preordered-Set
      strictly-preordered-set-ℕ
      strictly-preordered-set-ℕ
      strictly-preordered-set-ℕ
```

### Subsequences are functorial

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (u : sequence A)
  where

  map-subsequence : subsequence u → subsequence (map-sequence f u)
  map-subsequence H = H
```

### The extracted sequence of the image of a subsequence is the extracted sequence of the image

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (u : sequence A)
  (v : subsequence u)
  where

  compute-map-subsequence :
    Id
      (map-sequence f (seq-subsequence u v))
      (seq-subsequence (map-sequence f u) (map-subsequence f u v))
  compute-map-subsequence = refl
```

### The extraction sequence of a subsequence tends to infinity

```agda
module _
  {l : Level} {A : UU l} (u : sequence A) (v : subsequence u)
  where

  opaque
    is-unbounded-extract-subsequence :
      (M : ℕ) →
      Σ ( ℕ)
        ( λ N →
          (p : ℕ) →
          leq-ℕ N p →
          leq-ℕ M (extract-subsequence u v p))
    is-unbounded-extract-subsequence zero-ℕ =
      ( zero-ℕ , λ p K → leq-zero-ℕ (extract-subsequence u v p))
    is-unbounded-extract-subsequence (succ-ℕ M) =
      map-Σ
        ( λ N →
          (p : ℕ) →
          leq-ℕ N p →
          leq-ℕ
            ( succ-ℕ M)
            ( extract-subsequence u v p))
        ( succ-ℕ)
        ( λ N K p I →
          leq-succ-le-ℕ M (extract-subsequence u v p)
            ( concatenate-leq-le-ℕ
              { M}
              { extract-subsequence u v N}
              { extract-subsequence u v p}
              ( K N (refl-leq-ℕ N))
              ( is-strictly-increasing-extract-subsequence u v N p
                ( concatenate-le-leq-ℕ
                  { N}
                  { succ-ℕ N}
                  { p}
                  ( succ-le-ℕ N)
                  ( I)))))
        ( is-unbounded-extract-subsequence M)

  modulus-modulus-limit-∞-extract-subsequence : ℕ → ℕ
  modulus-modulus-limit-∞-extract-subsequence M =
    pr1 (is-unbounded-extract-subsequence M)

  is-modulus-modulus-limit-∞-extract-subsequence :
    is-modulus-limit-∞-sequence-Preorder
      ( ℕ-Preorder)
      ( extract-subsequence u v)
      ( modulus-modulus-limit-∞-extract-subsequence)
  is-modulus-modulus-limit-∞-extract-subsequence M =
    pr2 (is-unbounded-extract-subsequence M)

  modulus-limit-∞-extract-subsequence :
    modulus-limit-∞-sequence-Preorder ℕ-Preorder (extract-subsequence u v)
  modulus-limit-∞-extract-subsequence =
    modulus-modulus-limit-∞-extract-subsequence ,
    is-modulus-modulus-limit-∞-extract-subsequence

  is-limit-∞-extract-subsequence :
    is-limit-∞-sequence-Preorder ℕ-Preorder (extract-subsequence u v)
  is-limit-∞-extract-subsequence =
    unit-trunc-Prop modulus-limit-∞-extract-subsequence

  limit-∞-extract-subsequence : limit-∞-sequence-Preorder ℕ-Preorder
  limit-∞-extract-subsequence =
    extract-subsequence u v , is-limit-∞-extract-subsequence
```
