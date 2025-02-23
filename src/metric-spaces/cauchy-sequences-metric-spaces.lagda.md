# Cauchy sequences in metric spaces

```agda
{-# OPTIONS --lossy-unification #-}

module metric-spaces.cauchy-sequences-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.inequality-natural-numbers

open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.universe-levels
open import foundation.propositions

open import metric-spaces.cauchy-approximations-metric-spaces
open import metric-spaces.limits-of-cauchy-approximations-in-premetric-spaces
open import metric-spaces.metric-spaces
```

</details>

## Idea

A
{{#concept "Cauchy sequence" Disambiguation="in a metric space" Agda=is-cauchy-approximation-Metric-Space}}
`x` in a [metric space](metric-spaces.metric-spaces.md) is a mapping from the
[natural numbers](elementary-number-theory.natural-numbers.md) to the
underlying type of the metric space such that for any
[positive rational](elementary-number-theory.positive-rational-numbers.md) `ε`,
there is a concrete `n : ℕ` such that for any `m, k ≥ n`, `x m` and `x k` are
in a neighborhood of `ε` of each other.

Importantly, this is a structure, not a proposition, allowing us to explicitly
calculate rates of convergence.  This follows Section 11.2.2 in {{#cite UF13}}.

## Definition

### Cauchy sequences

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  (x : ℕ → type-Metric-Space M)
  where

  is-cauchy-sequence-Metric-Space : UU l2
  is-cauchy-sequence-Metric-Space =
    (ε : ℚ⁺) →
    Σ
      ( ℕ)
      ( λ n →
        (m k : ℕ) → leq-ℕ n m → leq-ℕ n k →
        neighborhood-Metric-Space M ε (x m) (x k))

module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  where

  cauchy-sequence-Metric-Space : UU (l1 ⊔ l2)
  cauchy-sequence-Metric-Space =
    Σ (ℕ → type-Metric-Space M) (is-cauchy-sequence-Metric-Space M)

  modulus-of-convergence-cauchy-sequence-Metric-Space :
    cauchy-sequence-Metric-Space → ℚ⁺ → ℕ
  modulus-of-convergence-cauchy-sequence-Metric-Space (x , is-cauchy-x) ε⁺ =
    pr1 (is-cauchy-x ε⁺)

  map-cauchy-sequence-Metric-Space :
    cauchy-sequence-Metric-Space → ℕ → type-Metric-Space M
  map-cauchy-sequence-Metric-Space = pr1

  is-cauchy-sequence-cauchy-sequence-Metric-Space :
    (x : cauchy-sequence-Metric-Space) →
    is-cauchy-sequence-Metric-Space M (map-cauchy-sequence-Metric-Space x)
  is-cauchy-sequence-cauchy-sequence-Metric-Space = pr2
```

### Limits of Cauchy sequences

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  (x : cauchy-sequence-Metric-Space M)
  (l : type-Metric-Space M)
  where

  is-limit-cauchy-sequence-Metric-Space : UU l2
  is-limit-cauchy-sequence-Metric-Space =
    (ε : ℚ⁺) →
    Σ
      ( ℕ)
      ( λ n →
        (m : ℕ) → leq-ℕ n m →
        neighborhood-Metric-Space
          ( M)
          ( ε)
          ( map-cauchy-sequence-Metric-Space M x m)
          ( l))
```

## Properties

### Correspondence with Cauchy approximations

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  (x : cauchy-sequence-Metric-Space M)
  where

  map-cauchy-approximation-cauchy-sequence-Metric-Space :
    ℚ⁺ → type-Metric-Space M
  map-cauchy-approximation-cauchy-sequence-Metric-Space ε =
    map-cauchy-sequence-Metric-Space
      ( M)
      ( x)
      ( modulus-of-convergence-cauchy-sequence-Metric-Space M x ε)

  is-cauchy-approximation-cauchy-approximation-cauchy-sequence-Metric-Space :
    is-cauchy-approximation-Metric-Space
      ( M)
      ( map-cauchy-approximation-cauchy-sequence-Metric-Space)
  is-cauchy-approximation-cauchy-approximation-cauchy-sequence-Metric-Space
    ε⁺@(ε , _) δ⁺@(δ , _) =
      rec-coproduct
        ( λ mε≤mδ →
          is-monotonic-structure-Metric-Space
            ( M)
            ( xmε)
            ( xmδ)
            ( ε⁺)
            ( ε⁺ +ℚ⁺ δ⁺)
            ( le-right-add-rational-ℚ⁺ ε δ⁺)
            ( pr2
              ( is-cauchy-sequence-cauchy-sequence-Metric-Space M x ε⁺)
              ( mε)
              ( mδ)
              ( refl-leq-ℕ mε)
              ( mε≤mδ)))
        ( λ mδ≤mε →
          is-monotonic-structure-Metric-Space
            ( M)
            ( xmε)
            ( xmδ)
            ( δ⁺)
            ( ε⁺ +ℚ⁺ δ⁺)
            ( le-left-add-rational-ℚ⁺ δ ε⁺)
            ( pr2
              ( is-cauchy-sequence-cauchy-sequence-Metric-Space M x δ⁺)
              ( mε)
              ( mδ)
              ( mδ≤mε)
              ( refl-leq-ℕ mδ)))
        ( linear-leq-ℕ mε mδ)
    where
      mε = modulus-of-convergence-cauchy-sequence-Metric-Space M x ε⁺
      mδ = modulus-of-convergence-cauchy-sequence-Metric-Space M x δ⁺
      xmε = map-cauchy-sequence-Metric-Space M x mε
      xmδ = map-cauchy-sequence-Metric-Space M x mδ

  cauchy-approximation-cauchy-sequence-Metric-Space :
    cauchy-approximation-Metric-Space M
  pr1 cauchy-approximation-cauchy-sequence-Metric-Space =
    map-cauchy-approximation-cauchy-sequence-Metric-Space
  pr2 cauchy-approximation-cauchy-sequence-Metric-Space =
    is-cauchy-approximation-cauchy-approximation-cauchy-sequence-Metric-Space
```

### The limit of a Cauchy approximation corresponding to a Cauchy sequence is the limit of the sequence

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  (x : cauchy-sequence-Metric-Space M)
  (l : type-Metric-Space M)
  (H :
    is-limit-cauchy-approximation-Premetric-Space
      ( premetric-Metric-Space M)
      ( cauchy-approximation-cauchy-sequence-Metric-Space M x)
      ( l))
  where

  is-limit-cauchy-sequence-limit-cauchy-approximation-cauchy-sequence-Metric-Space :
    is-limit-cauchy-sequence-Metric-Space M x l
  pr1
    ( is-limit-cauchy-sequence-limit-cauchy-approximation-cauchy-sequence-Metric-Space
      ε⁺@(ε , _)) =
        {! modulus-of-convergence-cauchy-sequence-Metric-Space M x ?  !}
```

## References

{­{#bibliography}}
