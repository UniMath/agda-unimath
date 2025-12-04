# Absolute convergence of series in real Banach spaces

```agda
module analysis.absolute-convergence-series-real-banach-spaces where
```

<details><summary>Imports</summary>

```agda
open import analysis.convergent-series-real-banach-spaces
open import analysis.convergent-series-real-numbers
open import analysis.series-real-banach-spaces
open import analysis.series-real-numbers

open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import linear-algebra.real-banach-spaces
open import linear-algebra.sums-of-finite-sequences-of-elements-real-banach-spaces

open import metric-spaces.cauchy-sequences-metric-spaces

open import order-theory.large-posets

open import real-numbers.cauchy-sequences-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.distance-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.rational-real-numbers
```

</details>

## Idea

A [series](analysis.series-real-banach-spaces.md) `Σ aₙ` in a
[real Banach space](linear-algebra.real-banach-spaces.md) is said to
{{#concept "absolutely converge" WDID=Q332465 WD="absolute convergence" Agda=is-absolutely-convergent-prop-series-ℝ-Banach-Space Disambiguation="series in a real Banach space"}}
if the series of norms `Σ ∥aₙ∥` is a
[convergent series](analysis.convergent-series-real-numbers.md) of
[real numbers](real-numbers.dedekind-real-numbers.md).

## Definition

```agda
module _
  {l1 l2 : Level}
  (V : ℝ-Banach-Space l1 l2)
  (σ : series-ℝ-Banach-Space V)
  where

  is-absolutely-convergent-prop-series-ℝ-Banach-Space : Prop (lsuc l1)
  is-absolutely-convergent-prop-series-ℝ-Banach-Space =
    is-convergent-prop-series-ℝ (map-norm-series-ℝ-Banach-Space V σ)

  is-absolutely-convergent-series-ℝ-Banach-Space : UU (lsuc l1)
  is-absolutely-convergent-series-ℝ-Banach-Space =
    type-Prop is-absolutely-convergent-prop-series-ℝ-Banach-Space
```

## Properties

### A Cauchy modulus for the sequence of partial sums of norms of terms in a series is a Cauchy modulus for the series

```agda
module _
  {l1 l2 : Level}
  (V : ℝ-Banach-Space l1 l2)
  (σ : series-ℝ-Banach-Space V)
  (M :
    is-cauchy-sequence-ℝ
      ( partial-sum-series-ℝ (map-norm-series-ℝ-Banach-Space V σ)))
  where

  abstract
    neighborhood-add-cauchy-modulus-partial-sum-norm-series-ℝ-Banach-Space :
      (ε : ℚ⁺) (n k : ℕ) → leq-ℕ (pr1 (M ε)) n →
      neighborhood-ℝ-Banach-Space
        ( V)
        ( ε)
        ( partial-sum-series-ℝ-Banach-Space V σ (n +ℕ k))
        ( partial-sum-series-ℝ-Banach-Space V σ n)
    neighborhood-add-cauchy-modulus-partial-sum-norm-series-ℝ-Banach-Space
      ε n k με≤n =
      let
        open inequality-reasoning-Large-Poset ℝ-Large-Poset
      in
        chain-of-inequalities
        dist-ℝ-Banach-Space V
          ( partial-sum-series-ℝ-Banach-Space V σ (n +ℕ k))
          ( partial-sum-series-ℝ-Banach-Space V σ n)
        ≤ map-norm-ℝ-Banach-Space V
            ( partial-sum-series-ℝ-Banach-Space V
              ( drop-series-ℝ-Banach-Space V n σ)
              ( k))
          by
            leq-eq-ℝ
              ( ap
                ( map-norm-ℝ-Banach-Space V)
                ( inv (partial-sum-drop-series-ℝ-Banach-Space V n σ k)))
        ≤ partial-sum-series-ℝ
            ( map-norm-series-ℝ-Banach-Space V
              ( drop-series-ℝ-Banach-Space V n σ))
            ( k)
          by
            triangle-inequality-norm-sum-fin-sequence-type-ℝ-Banach-Space
              ( V)
              ( k)
              ( _)
        ≤ ( partial-sum-series-ℝ
            ( map-norm-series-ℝ-Banach-Space V σ)
            ( n +ℕ k)) -ℝ
          ( partial-sum-series-ℝ (map-norm-series-ℝ-Banach-Space V σ) n)
          by
            leq-eq-ℝ
              ( partial-sum-drop-series-ℝ
                ( n)
                ( map-norm-series-ℝ-Banach-Space V σ)
                ( k))
        ≤ dist-ℝ
            ( partial-sum-series-ℝ
              ( map-norm-series-ℝ-Banach-Space V σ)
              ( n +ℕ k))
            ( partial-sum-series-ℝ
              ( map-norm-series-ℝ-Banach-Space V σ)
              ( n))
          by leq-diff-dist-ℝ _ _
        ≤ real-ℚ⁺ ε
          by
            leq-dist-neighborhood-ℝ
              ( ε)
              ( _)
              ( _)
              ( pr2
                ( M ε)
                ( n +ℕ k)
                ( n)
                ( transitive-leq-ℕ (pr1 (M ε)) n (n +ℕ k) (leq-add-ℕ n k) με≤n)
                ( με≤n))

    is-cauchy-partial-sum-is-cauchy-partial-sum-norm-series-ℝ-Banach-Space :
      is-cauchy-sequence-Metric-Space
        ( metric-space-ℝ-Banach-Space V)
        ( partial-sum-series-ℝ-Banach-Space V σ)
    is-cauchy-partial-sum-is-cauchy-partial-sum-norm-series-ℝ-Banach-Space =
      is-cauchy-sequence-modulus-neighborhood-add-sequence-Metric-Space
        ( metric-space-ℝ-Banach-Space V)
        ( partial-sum-series-ℝ-Banach-Space V σ)
        ( pr1 ∘ M)
        ( neighborhood-add-cauchy-modulus-partial-sum-norm-series-ℝ-Banach-Space)
```

### If a series is absolutely convergent, it is convergent

```agda
module _
  {l1 l2 : Level}
  (V : ℝ-Banach-Space l1 l2)
  (σ : series-ℝ-Banach-Space V)
  where

  is-convergent-is-absolutely-convergent-series-ℝ-Banach-Space :
    is-absolutely-convergent-series-ℝ-Banach-Space V σ →
    is-convergent-series-ℝ-Banach-Space V σ
  is-convergent-is-absolutely-convergent-series-ℝ-Banach-Space (lim-Σnorm , H) =
    let
      open
        do-syntax-trunc-Prop
          ( is-convergent-prop-series-ℝ-Banach-Space V σ)
    in do
      cauchy-mod ←
        exists-cauchy-modulus-has-limit-sequence-ℝ
          ( partial-sum-series-ℝ (map-norm-series-ℝ-Banach-Space V σ))
          ( lim-Σnorm , H)
      is-convergent-is-cauchy-sequence-partial-sum-series-ℝ-Banach-Space
        ( V)
        ( σ)
        ( is-cauchy-partial-sum-is-cauchy-partial-sum-norm-series-ℝ-Banach-Space
          ( V)
          ( σ)
          ( cauchy-mod))
```

## See also

- [Absolute convergence of series of real numbers](analysis.absolute-convergence-series-real-numbers.md)

## External links

- [Absolute convergence of series in Banach spaces](https://en.wikipedia.org/wiki/Absolute_convergence#Proof_that_any_absolutely_convergent_series_in_a_Banach_space_is_convergent)
  on Wikipedia
