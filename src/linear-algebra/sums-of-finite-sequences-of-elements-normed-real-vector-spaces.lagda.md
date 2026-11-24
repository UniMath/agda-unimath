# Sums of finite sequences of elements in normed real vector spaces

```agda
module linear-algebra.sums-of-finite-sequences-of-elements-normed-real-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.multiplication-positive-rational-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonzero-natural-numbers
open import elementary-number-theory.positive-rational-numbers

open import finite-group-theory.permutations-standard-finite-types

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels

open import linear-algebra.normed-real-vector-spaces
open import linear-algebra.sums-of-finite-sequences-of-elements-real-vector-spaces

open import lists.finite-sequences

open import metric-spaces.dependent-products-metric-spaces
open import metric-spaces.lipschitz-maps-metric-spaces
open import metric-spaces.uniformly-continuous-maps-metric-spaces

open import order-theory.large-posets

open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.inequalities-addition-and-subtraction-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.multiplication-nonnegative-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.sums-of-finite-sequences-of-nonnegative-real-numbers
open import real-numbers.sums-of-finite-sequences-of-real-numbers

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The
{{#concept "sum" Disambiguation="of a finite sequence of elements of a normed vector space over ℝ" Agda=sum-fin-sequence-type-Normed-ℝ-Vector-Space}}
of a [finite sequence](lists.finite-sequences.md) of elements of a
[normed vector space](linear-algebra.normed-real-vector-spaces.md) over the
[real numbers](real-numbers.dedekind-real-numbers.md) is the
[sum of the sequence](group-theory.sums-of-finite-sequences-of-elements-abelian-groups.md)
in the [abelian group](group-theory.abelian-groups.md) of the vector space under
addition.

## Definition

```agda
sum-fin-sequence-type-Normed-ℝ-Vector-Space :
  {l1 l2 : Level} (V : Normed-ℝ-Vector-Space l1 l2) (n : ℕ) →
  fin-sequence (type-Normed-ℝ-Vector-Space V) n → type-Normed-ℝ-Vector-Space V
sum-fin-sequence-type-Normed-ℝ-Vector-Space (V , _) =
  sum-fin-sequence-type-ℝ-Vector-Space V
```

## Properties

### Homotopies preserve sums

```agda
module _
  {l1 l2 : Level}
  (V : Normed-ℝ-Vector-Space l1 l2)
  where

  abstract
    htpy-sum-fin-sequence-type-Normed-ℝ-Vector-Space :
      (n : ℕ) {f g : fin-sequence (type-Normed-ℝ-Vector-Space V) n} → f ~ g →
      sum-fin-sequence-type-Normed-ℝ-Vector-Space V n f ＝
      sum-fin-sequence-type-Normed-ℝ-Vector-Space V n g
    htpy-sum-fin-sequence-type-Normed-ℝ-Vector-Space =
      htpy-sum-fin-sequence-type-ℝ-Vector-Space
        ( vector-space-Normed-ℝ-Vector-Space V)
```

### Permutations preserve sums

```agda
module _
  {l1 l2 : Level}
  (V : Normed-ℝ-Vector-Space l1 l2)
  where

  abstract
    preserves-sum-permutation-fin-sequence-type-Normed-ℝ-Vector-Space :
      (n : ℕ) (σ : Permutation n)
      (u : fin-sequence (type-Normed-ℝ-Vector-Space V) n) →
      sum-fin-sequence-type-Normed-ℝ-Vector-Space V n u ＝
      sum-fin-sequence-type-Normed-ℝ-Vector-Space V n (u ∘ map-equiv σ)
    preserves-sum-permutation-fin-sequence-type-Normed-ℝ-Vector-Space =
      preserves-sum-permutation-fin-sequence-type-ℝ-Vector-Space
        ( vector-space-Normed-ℝ-Vector-Space V)
```

### Interchanging sums and addition

```agda
module _
  {l1 l2 : Level}
  (V : Normed-ℝ-Vector-Space l1 l2)
  where

  abstract
    interchange-sum-add-fin-sequence-type-Normed-ℝ-Vector-Space :
      (n : ℕ) (f g : fin-sequence (type-Normed-ℝ-Vector-Space V) n) →
      sum-fin-sequence-type-Normed-ℝ-Vector-Space V
        ( n)
        ( λ i → add-Normed-ℝ-Vector-Space V (f i) (g i)) ＝
      add-Normed-ℝ-Vector-Space V
        ( sum-fin-sequence-type-Normed-ℝ-Vector-Space V n f)
        ( sum-fin-sequence-type-Normed-ℝ-Vector-Space V n g)
    interchange-sum-add-fin-sequence-type-Normed-ℝ-Vector-Space =
      interchange-sum-add-fin-sequence-type-ℝ-Vector-Space
        ( vector-space-Normed-ℝ-Vector-Space V)
```

### Interchanging sums and subtraction

```agda
module _
  {l1 l2 : Level}
  (V : Normed-ℝ-Vector-Space l1 l2)
  where

  abstract
    interchange-sum-diff-fin-sequence-type-Normed-ℝ-Vector-Space :
      (n : ℕ) (f g : fin-sequence (type-Normed-ℝ-Vector-Space V) n) →
      sum-fin-sequence-type-Normed-ℝ-Vector-Space V
        ( n)
        ( λ i → diff-Normed-ℝ-Vector-Space V (f i) (g i)) ＝
      diff-Normed-ℝ-Vector-Space V
        ( sum-fin-sequence-type-Normed-ℝ-Vector-Space V n f)
        ( sum-fin-sequence-type-Normed-ℝ-Vector-Space V n g)
    interchange-sum-diff-fin-sequence-type-Normed-ℝ-Vector-Space =
      interchange-sum-diff-fin-sequence-type-ℝ-Vector-Space
        ( vector-space-Normed-ℝ-Vector-Space V)
```

### Multiplication is distributive over sums

```agda
module _
  {l1 l2 : Level}
  (V : Normed-ℝ-Vector-Space l1 l2)
  where

  abstract
    left-distributive-mul-sum-fin-sequence-type-Normed-ℝ-Vector-Space :
      (n : ℕ) (c : ℝ l1) (u : fin-sequence (type-Normed-ℝ-Vector-Space V) n) →
      mul-Normed-ℝ-Vector-Space V
        ( c)
        ( sum-fin-sequence-type-Normed-ℝ-Vector-Space V n u) ＝
      sum-fin-sequence-type-Normed-ℝ-Vector-Space V
        ( n)
        ( mul-Normed-ℝ-Vector-Space V c ∘ u)
    left-distributive-mul-sum-fin-sequence-type-Normed-ℝ-Vector-Space =
      left-distributive-mul-sum-fin-sequence-type-ℝ-Vector-Space
        ( vector-space-Normed-ℝ-Vector-Space V)
```

### Negation is distributive over sums

```agda
module _
  {l1 l2 : Level}
  (V : Normed-ℝ-Vector-Space l1 l2)
  where

  abstract
    distributive-neg-sum-fin-sequence-type-Normed-ℝ-Vector-Space :
      (n : ℕ) (u : fin-sequence (type-Normed-ℝ-Vector-Space V) n) →
      neg-Normed-ℝ-Vector-Space V
        ( sum-fin-sequence-type-Normed-ℝ-Vector-Space V n u) ＝
      sum-fin-sequence-type-Normed-ℝ-Vector-Space V
        ( n)
        ( neg-Normed-ℝ-Vector-Space V ∘ u)
    distributive-neg-sum-fin-sequence-type-Normed-ℝ-Vector-Space =
      distributive-neg-sum-fin-sequence-type-ℝ-Vector-Space
        ( vector-space-Normed-ℝ-Vector-Space V)
```

### The norm of the sum of a finite sequence is at most the sum of the norms of the terms of the sequence

```agda
module _
  {l1 l2 : Level}
  (V : Normed-ℝ-Vector-Space l1 l2)
  where

  abstract
    triangle-inequality-norm-sum-fin-sequence-type-Normed-ℝ-Vector-Space :
      (n : ℕ) (σ : fin-sequence (type-Normed-ℝ-Vector-Space V) n) →
      leq-ℝ
        ( map-norm-Normed-ℝ-Vector-Space V
          ( sum-fin-sequence-type-Normed-ℝ-Vector-Space V n σ))
        ( sum-fin-sequence-ℝ n (map-norm-Normed-ℝ-Vector-Space V ∘ σ))
    triangle-inequality-norm-sum-fin-sequence-type-Normed-ℝ-Vector-Space 0 σ =
      leq-eq-ℝ (eq-zero-norm-zero-Normed-ℝ-Vector-Space V)
    triangle-inequality-norm-sum-fin-sequence-type-Normed-ℝ-Vector-Space
      (succ-ℕ n) σ =
      let
        open inequality-reasoning-Large-Poset ℝ-Large-Poset
      in
        chain-of-inequalities
          map-norm-Normed-ℝ-Vector-Space V
            ( sum-fin-sequence-type-Normed-ℝ-Vector-Space V (succ-ℕ n) σ)
          ≤ ( map-norm-Normed-ℝ-Vector-Space V
              ( sum-fin-sequence-type-Normed-ℝ-Vector-Space V
                ( n)
                ( σ ∘ inl-Fin n))) +ℝ
            ( map-norm-Normed-ℝ-Vector-Space V (σ (neg-one-Fin n)))
            by triangular-norm-Normed-ℝ-Vector-Space V _ _
          ≤ sum-fin-sequence-ℝ (succ-ℕ n) (map-norm-Normed-ℝ-Vector-Space V ∘ σ)
            by
              preserves-leq-right-add-ℝ _ _ _
                ( triangle-inequality-norm-sum-fin-sequence-type-Normed-ℝ-Vector-Space
                  ( n)
                  ( σ ∘ inl-Fin n))
```

### The sum operation is a Lipschitz map

```agda
module _
  {l1 l2 : Level}
  (V : Normed-ℝ-Vector-Space l1 l2)
  (n : ℕ)
  where

  lipschitz-constant-sum-fin-sequence-type-Normed-ℝ-Vector-Space : ℚ⁺
  lipschitz-constant-sum-fin-sequence-type-Normed-ℝ-Vector-Space =
    positive-rational-ℕ⁺ (succ-nonzero-ℕ' n)

  abstract
    is-lipschitz-constant-lipschitz-constant-sum-fin-sequence-type-Normed-ℝ-Vector-Space :
      is-lipschitz-constant-map-Metric-Space
        ( Π-Metric-Space (Fin n) (λ _ → metric-space-Normed-ℝ-Vector-Space V))
        ( metric-space-Normed-ℝ-Vector-Space V)
        ( sum-fin-sequence-type-Normed-ℝ-Vector-Space V n)
        ( lipschitz-constant-sum-fin-sequence-type-Normed-ℝ-Vector-Space)
    is-lipschitz-constant-lipschitz-constant-sum-fin-sequence-type-Normed-ℝ-Vector-Space
      ε u v ∥uᵢ-vᵢ∥≤ε =
      let
        open inequality-reasoning-Large-Poset ℝ-Large-Poset
      in
        chain-of-inequalities
          dist-Normed-ℝ-Vector-Space V
            ( sum-fin-sequence-type-Normed-ℝ-Vector-Space V n u)
            ( sum-fin-sequence-type-Normed-ℝ-Vector-Space V n v)
          ≤ map-norm-Normed-ℝ-Vector-Space
              ( V)
              ( sum-fin-sequence-type-Normed-ℝ-Vector-Space V
                ( n)
                ( λ i → diff-Normed-ℝ-Vector-Space V (u i) (v i)))
            by
              leq-eq-ℝ
                ( ap
                  ( map-norm-Normed-ℝ-Vector-Space V)
                  ( inv
                    ( interchange-sum-diff-fin-sequence-type-Normed-ℝ-Vector-Space
                      ( V)
                      ( n)
                      ( u)
                      ( v))))
          ≤ sum-fin-sequence-ℝ
              ( n)
              ( λ i → dist-Normed-ℝ-Vector-Space V (u i) (v i))
            by
              triangle-inequality-norm-sum-fin-sequence-type-Normed-ℝ-Vector-Space
                ( V)
                ( n)
                ( _)
          ≤ real-ℕ n *ℝ real-ℚ⁺ ε
            by
              leq-mul-bound-sum-fin-sequence-ℝ⁰⁺
                ( n)
                ( λ i → nonnegative-dist-Normed-ℝ-Vector-Space V (u i) (v i))
                ( nonnegative-real-ℚ⁺ ε)
                ( ∥uᵢ-vᵢ∥≤ε)
          ≤ real-ℕ (succ-ℕ n) *ℝ real-ℚ⁺ ε
            by
              preserves-leq-right-mul-ℝ⁰⁺
                ( nonnegative-real-ℚ⁺ ε)
                ( preserves-leq-real-ℕ (succ-leq-ℕ n))
          ≤ real-ℚ⁺ (positive-rational-ℕ⁺ (succ-nonzero-ℕ' n) *ℚ⁺ ε)
            by leq-eq-ℝ (mul-real-ℚ _ _)

  is-lipschitz-sum-fin-sequence-type-Normed-ℝ-Vector-Space :
    is-lipschitz-map-Metric-Space
      ( Π-Metric-Space (Fin n) (λ _ → metric-space-Normed-ℝ-Vector-Space V))
      ( metric-space-Normed-ℝ-Vector-Space V)
      ( sum-fin-sequence-type-Normed-ℝ-Vector-Space V n)
  is-lipschitz-sum-fin-sequence-type-Normed-ℝ-Vector-Space =
    intro-exists
      ( lipschitz-constant-sum-fin-sequence-type-Normed-ℝ-Vector-Space)
      ( is-lipschitz-constant-lipschitz-constant-sum-fin-sequence-type-Normed-ℝ-Vector-Space)

  abstract
    is-uniformly-continuous-sum-fin-sequence-type-Normed-ℝ-Vector-Space :
      is-uniformly-continuous-map-Metric-Space
        ( Π-Metric-Space (Fin n) (λ _ → metric-space-Normed-ℝ-Vector-Space V))
        ( metric-space-Normed-ℝ-Vector-Space V)
        ( sum-fin-sequence-type-Normed-ℝ-Vector-Space V n)
    is-uniformly-continuous-sum-fin-sequence-type-Normed-ℝ-Vector-Space =
      is-uniformly-continuous-map-is-lipschitz-map-Metric-Space
        ( Π-Metric-Space (Fin n) (λ _ → metric-space-Normed-ℝ-Vector-Space V))
        ( metric-space-Normed-ℝ-Vector-Space V)
        ( sum-fin-sequence-type-Normed-ℝ-Vector-Space V n)
        ( is-lipschitz-sum-fin-sequence-type-Normed-ℝ-Vector-Space)

  uniformly-continuous-sum-fin-sequence-type-Normed-ℝ-Vector-Space :
    uniformly-continuous-map-Metric-Space
      ( Π-Metric-Space (Fin n) (λ _ → metric-space-Normed-ℝ-Vector-Space V))
      ( metric-space-Normed-ℝ-Vector-Space V)
  uniformly-continuous-sum-fin-sequence-type-Normed-ℝ-Vector-Space =
    ( sum-fin-sequence-type-Normed-ℝ-Vector-Space V n ,
      is-uniformly-continuous-sum-fin-sequence-type-Normed-ℝ-Vector-Space)
```
