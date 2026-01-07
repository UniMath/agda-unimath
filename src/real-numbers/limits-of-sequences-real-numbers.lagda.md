# Limits of sequences in the real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.limits-of-sequences-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.universe-levels

open import lists.sequences
open import lists.subsequences

open import metric-spaces.cartesian-products-metric-spaces
open import metric-spaces.limits-of-sequences-metric-spaces

open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.inequalities-addition-and-subtraction-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.isometry-addition-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.strict-inequalities-addition-and-subtraction-real-numbers
open import real-numbers.strict-inequality-real-numbers
open import real-numbers.uniformly-continuous-endomaps-real-numbers
```

</details>

## Idea

On this page, we describe properties of
[limits of sequences](metric-spaces.limits-of-sequences-metric-spaces.md) in the
[metric space of real numbers](real-numbers.metric-space-of-real-numbers.md).

## Definition

```agda
is-limit-prop-sequence-ℝ : {l : Level} → sequence (ℝ l) → ℝ l → Prop l
is-limit-prop-sequence-ℝ {l} =
  is-limit-prop-sequence-Metric-Space (metric-space-ℝ l)

is-limit-sequence-ℝ : {l : Level} → sequence (ℝ l) → ℝ l → UU l
is-limit-sequence-ℝ {l} = is-limit-sequence-Metric-Space (metric-space-ℝ l)

has-limit-prop-sequence-ℝ : {l : Level} → sequence (ℝ l) → Prop (lsuc l)
has-limit-prop-sequence-ℝ {l} =
  has-limit-prop-sequence-Metric-Space (metric-space-ℝ l)

has-limit-sequence-ℝ : {l : Level} → sequence (ℝ l) → UU (lsuc l)
has-limit-sequence-ℝ u = type-Prop (has-limit-prop-sequence-ℝ u)
```

## Properties

### Any two limits of a sequence of real numbers are equal

```agda
module _
  {l : Level}
  (σ : sequence (ℝ l))
  where

  abstract
    eq-is-limit-sequence-ℝ :
      (a b : ℝ l) → is-limit-sequence-ℝ σ a → is-limit-sequence-ℝ σ b → a ＝ b
    eq-is-limit-sequence-ℝ =
      eq-limit-sequence-Metric-Space
        ( metric-space-ℝ l)
        ( σ)
```

### If two sequences have a limit, their sum has a limit equal to the sum of the limits

```agda
module _
  {l1 l2 : Level}
  {u : sequence (ℝ l1)}
  {v : sequence (ℝ l2)}
  {lim-u : ℝ l1}
  {lim-v : ℝ l2}
  (Hu : is-limit-sequence-ℝ u lim-u)
  (Hv : is-limit-sequence-ℝ v lim-v)
  where

  abstract
    is-limit-add-sequence-ℝ :
      is-limit-sequence-Metric-Space
        ( metric-space-ℝ (l1 ⊔ l2))
        ( binary-map-sequence add-ℝ u v)
        ( lim-u +ℝ lim-v)
    is-limit-add-sequence-ℝ =
      is-limit-map-sequence-modulated-ucont-map-Metric-Space
        ( product-Metric-Space (metric-space-ℝ l1) (metric-space-ℝ l2))
        ( metric-space-ℝ (l1 ⊔ l2))
        ( modulated-ucont-map-add-pair-ℝ l1 l2)
        ( pair-sequence u v)
        ( lim-u , lim-v)
        ( is-limit-pair-sequence-Metric-Space
          ( metric-space-ℝ l1)
          ( metric-space-ℝ l2)
          ( Hu)
          ( Hv))
```

### Uniformly continuous functions from `ℝ` to `ℝ` preserve limits

```agda
module _
  {l1 l2 : Level}
  (f : uniformly-continuous-endomap-ℝ l1 l2)
  (u : sequence (ℝ l1))
  (lim : ℝ l1)
  where

  abstract
    is-limit-map-sequence-uniformly-continuous-endomap-ℝ :
      is-limit-sequence-ℝ u lim →
      is-limit-sequence-ℝ
        ( map-sequence
          ( map-uniformly-continuous-endomap-ℝ f)
          ( u))
        ( map-uniformly-continuous-endomap-ℝ f lim)
    is-limit-map-sequence-uniformly-continuous-endomap-ℝ =
      is-limit-map-sequence-uniformly-continuous-map-Metric-Space
        ( metric-space-ℝ l1)
        ( metric-space-ℝ l2)
        ( f)
        ( u)
        ( lim)
```

### A lower bound on a sequence is a lower bound on its limit

```agda
module _
  {l1 l2 : Level}
  (b : ℝ l1)
  {u : sequence (ℝ l2)}
  {lim-u : ℝ l2}
  where

  abstract
    lower-bound-lim-lower-bound-sequence-ℝ :
      ((n : ℕ) → leq-ℝ b (u n)) → is-limit-sequence-ℝ u lim-u →
      leq-ℝ b lim-u
    lower-bound-lim-lower-bound-sequence-ℝ H =
      elim-exists
        ( leq-prop-ℝ b lim-u)
        ( λ μ is-mod-μ →
          leq-not-le-ℝ
            ( lim-u)
            ( b)
            ( λ lim-u<b →
              let
                open do-syntax-trunc-Prop empty-Prop
              in do
                (ε , lim-u+ε<b) ←
                  exists-positive-rational-separation-le-ℝ lim-u<b
                not-leq-le-ℝ
                  ( u (μ ε))
                  ( b)
                  ( concatenate-leq-le-ℝ
                    ( u (μ ε))
                    ( lim-u +ℝ real-ℚ⁺ ε)
                    ( b)
                    ( left-leq-real-bound-neighborhood-ℝ
                      ( ε)
                      ( u (μ ε))
                      ( lim-u)
                      ( is-mod-μ
                        ( ε)
                        ( μ ε)
                        ( refl-leq-ℕ (μ ε))))
                    ( lim-u+ε<b))
                  ( H (μ ε))))
```

### An upper bound on a sequence is an upper bound on its limit

```agda
module _
  {l1 l2 : Level}
  (b : ℝ l1)
  {u : sequence (ℝ l2)}
  {lim-u : ℝ l2}
  where

  abstract
    upper-bound-lim-upper-bound-sequence-ℝ :
      ((n : ℕ) → leq-ℝ (u n) b) → is-limit-sequence-ℝ u lim-u →
      leq-ℝ lim-u b
    upper-bound-lim-upper-bound-sequence-ℝ H =
      elim-exists
        ( leq-prop-ℝ lim-u b)
        ( λ μ is-mod-μ →
          leq-not-le-ℝ
            ( b)
            ( lim-u)
            ( λ b<lim-u →
              let
                open do-syntax-trunc-Prop empty-Prop
              in do
                (ε , b+ε<lim-u) ←
                  exists-positive-rational-separation-le-ℝ b<lim-u
                not-leq-le-ℝ
                  ( b)
                  ( u (μ ε))
                  ( concatenate-le-leq-ℝ
                    ( b)
                    ( lim-u -ℝ real-ℚ⁺ ε)
                    ( u (μ ε))
                    ( le-transpose-left-add-ℝ _ _ _ b+ε<lim-u)
                    ( leq-transpose-right-add-ℝ _ _ _
                      ( right-leq-real-bound-neighborhood-ℝ
                        ( ε)
                        ( u (μ ε))
                        ( lim-u)
                        ( is-mod-μ
                          ( ε)
                          ( μ ε)
                          ( refl-leq-ℕ (μ ε))))))
                  ( H (μ ε))))
```

### Taking subsequences preserves limits

```agda
module _
  {l : Level}
  {u : sequence (ℝ l)}
  {lim-u : ℝ l}
  (v : subsequence u)
  where

  abstract
    is-limit-subsequence-ℝ :
      is-limit-sequence-ℝ u lim-u →
      is-limit-sequence-ℝ (seq-subsequence u v) lim-u
    is-limit-subsequence-ℝ =
      is-limit-subsequence-Metric-Space (metric-space-ℝ l) v
```
