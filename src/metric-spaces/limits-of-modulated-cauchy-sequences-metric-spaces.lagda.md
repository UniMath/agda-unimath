# Limits of modulated Cauchy sequences in metric spaces

```agda
{-# OPTIONS --lossy-unification #-}

module metric-spaces.limits-of-modulated-cauchy-sequences-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.maximum-natural-numbers
open import elementary-number-theory.multiplicative-group-of-positive-rational-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonzero-natural-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.strict-inequality-natural-numbers
open import elementary-number-theory.strict-inequality-positive-rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers
open import elementary-number-theory.unit-fractions-rational-numbers

open import foundation.dependent-pair-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.cauchy-approximations-metric-spaces
open import metric-spaces.limits-of-cauchy-approximations-metric-spaces
open import metric-spaces.limits-of-sequences-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.modulated-cauchy-sequences-metric-spaces
```

</details>

## Idea

This page describes properties of the
[limits](metric-spaces.limits-of-sequences-metric-spaces.md) of
[modulated Cauchy sequences](metric-spaces.modulated-cauchy-sequences-metric-spaces.md)
in [metric spaces](metric-spaces.metric-spaces.md).

## Definition

```agda
module _
  {l1 l2 : Level}
  (M : Metric-Space l1 l2)
  (x : modulated-cauchy-sequence-Metric-Space M)
  where

  is-limit-modulus-prop-modulated-cauchy-sequence-Metric-Space :
    type-Metric-Space M → (ℚ⁺ → ℕ) → Prop l2
  is-limit-modulus-prop-modulated-cauchy-sequence-Metric-Space =
    is-limit-modulus-prop-sequence-Metric-Space
      ( M)
      ( sequence-modulated-cauchy-sequence-Metric-Space M x)

  is-limit-modulus-modulated-cauchy-sequence-Metric-Space :
    type-Metric-Space M → (ℚ⁺ → ℕ) → UU l2
  is-limit-modulus-modulated-cauchy-sequence-Metric-Space lim μ =
    type-Prop
      ( is-limit-modulus-prop-modulated-cauchy-sequence-Metric-Space lim μ)

  limit-modulus-sequence-modulated-cauchy-sequence-Metric-Space :
    type-Metric-Space M → UU l2
  limit-modulus-sequence-modulated-cauchy-sequence-Metric-Space lim =
    type-subtype
      ( is-limit-modulus-prop-modulated-cauchy-sequence-Metric-Space lim)

  is-limit-prop-modulated-cauchy-sequence-Metric-Space :
    type-Metric-Space M → Prop l2
  is-limit-prop-modulated-cauchy-sequence-Metric-Space =
    is-limit-prop-sequence-Metric-Space
      ( M)
      ( sequence-modulated-cauchy-sequence-Metric-Space M x)

  is-limit-modulated-cauchy-sequence-Metric-Space : type-Metric-Space M → UU l2
  is-limit-modulated-cauchy-sequence-Metric-Space lim =
    type-Prop (is-limit-prop-modulated-cauchy-sequence-Metric-Space lim)

  has-limit-prop-modulated-cauchy-sequence-Metric-Space : Prop (l1 ⊔ l2)
  has-limit-prop-modulated-cauchy-sequence-Metric-Space =
    has-limit-prop-sequence-Metric-Space
      ( M)
      ( sequence-modulated-cauchy-sequence-Metric-Space M x)

  has-limit-modulated-cauchy-sequence-Metric-Space : UU (l1 ⊔ l2)
  has-limit-modulated-cauchy-sequence-Metric-Space =
    type-Prop has-limit-prop-modulated-cauchy-sequence-Metric-Space
```

## Properties

### The limit of a Cauchy approximation corresponding to a modulated Cauchy sequence is the limit of the sequence

```agda
module _
  {l1 l2 : Level}
  (M : Metric-Space l1 l2)
  (x : modulated-cauchy-sequence-Metric-Space M)
  (lim : type-Metric-Space M)
  (H :
    is-limit-cauchy-approximation-Metric-Space
      ( M)
      ( cauchy-approximation-modulated-cauchy-sequence-Metric-Space M x)
      ( lim))
  where

  modulus-cauchy-sequence-limit-cauchy-approximation-modulated-cauchy-sequence-Metric-Space :
    ℚ⁺ → ℕ
  modulus-cauchy-sequence-limit-cauchy-approximation-modulated-cauchy-sequence-Metric-Space
    ε⁺@(ε , _) =
      let
        (ε'⁺@(ε' , _) , 2ε'<ε) = bound-double-le-ℚ⁺ ε⁺
        ε''⁺@(ε'' , _) = left-summand-split-ℚ⁺ ε'⁺
      in
        map-modulus-modulated-cauchy-sequence-Metric-Space M x ε''⁺

  abstract
    is-limit-modulus-cauchy-sequence-limit-cauchy-approximation-modulated-cauchy-sequence-Metric-Space :
      is-limit-modulus-modulated-cauchy-sequence-Metric-Space
        ( M)
        ( x)
        ( lim)
        ( modulus-cauchy-sequence-limit-cauchy-approximation-modulated-cauchy-sequence-Metric-Space)
    is-limit-modulus-cauchy-sequence-limit-cauchy-approximation-modulated-cauchy-sequence-Metric-Space
      ε⁺@(ε , _) m n≤m =
      let
        (ε'⁺@(ε' , _) , 2ε'<ε) = bound-double-le-ℚ⁺ ε⁺
        ε''⁺@(ε'' , _) = left-summand-split-ℚ⁺ ε'⁺
        n =
          map-modulus-modulated-cauchy-sequence-Metric-Space M x ε''⁺
        xn = sequence-modulated-cauchy-sequence-Metric-Space M x n
        xm = sequence-modulated-cauchy-sequence-Metric-Space M x m
      in
        monotonic-neighborhood-Metric-Space
          ( M)
          ( xm)
          ( lim)
          ( ε''⁺ +ℚ⁺ ε'⁺)
          ( ε⁺)
          ( transitive-le-ℚ
            ( ε'' +ℚ ε')
            ( ε' +ℚ ε')
            ( ε)
            ( 2ε'<ε)
            ( preserves-le-left-add-ℚ ε' ε'' ε' (le-mediant-zero-ℚ⁺ ε'⁺)))
          ( triangular-neighborhood-Metric-Space
            ( M)
            ( xm)
            ( xn)
            ( lim)
            ( ε''⁺)
            ( ε'⁺)
            ( tr
              ( λ d → neighborhood-Metric-Space M d xn lim)
              ( eq-add-split-ℚ⁺ ε'⁺)
              ( H ε''⁺ (right-summand-split-ℚ⁺ ε'⁺)))
            ( symmetric-neighborhood-Metric-Space
              ( M)
              ( ε''⁺)
              ( xn)
              ( xm)
              ( neighborhood-at-map-modulus-modulated-cauchy-sequence-Metric-Space
                ( M)
                ( x)
                ( ε''⁺)
                ( m)
                ( n≤m))))

    is-limit-modulated-cauchy-sequence-limit-cauchy-approximation-modulated-cauchy-sequence-Metric-Space :
      is-limit-modulated-cauchy-sequence-Metric-Space M x lim
    is-limit-modulated-cauchy-sequence-limit-cauchy-approximation-modulated-cauchy-sequence-Metric-Space =
      unit-trunc-Prop
        ( modulus-cauchy-sequence-limit-cauchy-approximation-modulated-cauchy-sequence-Metric-Space ,
          is-limit-modulus-cauchy-sequence-limit-cauchy-approximation-modulated-cauchy-sequence-Metric-Space)

    has-limit-modulated-cauchy-sequence-limit-cauchy-approximation-modulated-cauchy-sequence-Metric-Space :
      has-limit-modulated-cauchy-sequence-Metric-Space M x
    has-limit-modulated-cauchy-sequence-limit-cauchy-approximation-modulated-cauchy-sequence-Metric-Space =
      ( lim ,
        is-limit-modulated-cauchy-sequence-limit-cauchy-approximation-modulated-cauchy-sequence-Metric-Space)
```

### If a Cauchy approximation has a limit, its corresponding modulated Cauchy sequence has the same limit

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  (x : cauchy-approximation-Metric-Space M)
  (lim : type-Metric-Space M)
  (is-lim : is-limit-cauchy-approximation-Metric-Space M x lim)
  where

  abstract
    is-limit-modulated-cauchy-sequence-cauchy-approximation-Metric-Space :
      is-limit-modulated-cauchy-sequence-Metric-Space
        ( M)
        ( modulated-cauchy-sequence-cauchy-approximation-Metric-Space M x)
        ( lim)
    is-limit-modulated-cauchy-sequence-cauchy-approximation-Metric-Space =
      is-limit-bound-modulus-sequence-Metric-Space M _ _
        ( λ ε →
          let
            (n⁺ , 1/n⁺<ε) = smaller-reciprocal-ℚ⁺ ε
          in
            ( nat-nonzero-ℕ n⁺ ,
              λ m n≤m →
              monotonic-neighborhood-Metric-Space M
                ( seq-modulated-cauchy-sequence-cauchy-approximation-Metric-Space
                  ( M)
                  ( x)
                  ( m))
                ( lim)
                ( positive-reciprocal-rational-succ-ℕ m)
                ( ε)
                ( transitive-le-ℚ _ (reciprocal-rational-ℕ⁺ n⁺) _
                  ( 1/n⁺<ε)
                  ( inv-le-ℚ⁺
                    ( positive-rational-ℕ⁺ n⁺)
                    ( positive-rational-ℕ⁺ (succ-nonzero-ℕ' m))
                    ( preserves-le-rational-ℕ
                      ( le-succ-leq-ℕ _ _ n≤m))))
                ( saturated-is-limit-cauchy-approximation-Metric-Space M
                  ( x)
                  ( lim)
                  ( is-lim)
                  ( positive-reciprocal-rational-succ-ℕ m))))
```

### If the modulated Cauchy sequence associated with a Cauchy approximation has a limit modulus at `l`, its associated approximation converges to `l`

```agda
module _
  { l1 l2 : Level} (M : Metric-Space l1 l2)
  ( x : cauchy-approximation-Metric-Space M)
  ( lim : type-Metric-Space M)
  ( H :
    limit-modulus-sequence-modulated-cauchy-sequence-Metric-Space
      ( M)
      ( modulated-cauchy-sequence-cauchy-approximation-Metric-Space M x)
      ( lim))
  where

  abstract
    is-limit-cauchy-approximation-limit-modulus-modulated-cauchy-sequence-cauchy-approximation-Metric-Space :
      is-limit-cauchy-approximation-Metric-Space M x lim
    is-limit-cauchy-approximation-limit-modulus-modulated-cauchy-sequence-cauchy-approximation-Metric-Space
      ε⁺@(ε , _) δ⁺@(δ , _) =
      let
        (δ'⁺@(δ' , _) , 2δ'<δ) = bound-double-le-ℚ⁺ δ⁺
        (n₁' , 1/n₁'<δ') = smaller-reciprocal-ℚ⁺ δ'⁺
        1/n₁' = positive-reciprocal-rational-ℕ⁺ n₁'
        n₁ = pred-ℕ⁺ n₁'
        n₂ =
          modulus-limit-modulus-sequence-Metric-Space
            ( M)
            ( seq-modulated-cauchy-sequence-cauchy-approximation-Metric-Space
              ( M)
              ( x))
            ( lim)
            ( H)
            ( δ'⁺)
        n = max-ℕ n₁ n₂
        n' = succ-nonzero-ℕ' n
        1/n' = positive-reciprocal-rational-ℕ⁺ n'
        xε = map-cauchy-approximation-Metric-Space M x ε⁺
        x1/n' = map-cauchy-approximation-Metric-Space M x 1/n'
        x1/n'-l-neighborhood : neighborhood-Metric-Space M δ'⁺ x1/n' lim
        x1/n'-l-neighborhood =
          is-modulus-limit-modulus-sequence-Metric-Space
            ( M)
            ( sequence-modulated-cauchy-sequence-Metric-Space
              ( M)
              ( modulated-cauchy-sequence-cauchy-approximation-Metric-Space
                ( M)
                ( x)))
            ( lim)
            ( H)
            ( δ'⁺)
            ( n)
            ( right-leq-max-ℕ n₁ n₂)
      in
        monotonic-neighborhood-Metric-Space
          ( M)
          ( xε)
          ( lim)
          ( (ε⁺ +ℚ⁺ δ'⁺) +ℚ⁺ δ'⁺)
          ( ε⁺ +ℚ⁺ δ⁺)
          ( inv-tr
            ( λ y → le-ℚ⁺ y (ε⁺ +ℚ⁺ δ⁺))
            ( associative-add-ℚ⁺ ε⁺ δ'⁺ δ'⁺)
            ( preserves-le-right-add-ℚ ε (δ' +ℚ δ') δ 2δ'<δ))
          ( triangular-neighborhood-Metric-Space
            ( M)
            ( xε)
            ( x1/n')
            ( lim)
            ( ε⁺ +ℚ⁺ δ'⁺)
            ( δ'⁺)
            ( x1/n'-l-neighborhood)
            ( monotonic-neighborhood-Metric-Space
              ( M)
              ( xε)
              ( x1/n')
              ( ε⁺ +ℚ⁺ 1/n')
              ( ε⁺ +ℚ⁺ δ'⁺)
              ( preserves-le-right-add-ℚ
                ( ε)
                ( rational-ℚ⁺ 1/n')
                ( δ')
                ( concatenate-leq-le-ℚ
                  ( rational-ℚ⁺ 1/n')
                  ( rational-ℚ⁺ 1/n₁')
                  ( δ')
                  ( leq-reciprocal-rational-ℕ⁺
                    ( n₁')
                    ( n')
                    ( reflects-leq-pred-nonzero-ℕ
                      ( n₁')
                      ( n')
                      ( inv-tr
                        ( leq-ℕ n₁)
                        ( is-section-pred-nonzero-ℕ n)
                        ( left-leq-max-ℕ n₁ n₂))))
                  ( 1/n₁'<δ')))
              ( is-cauchy-approximation-map-cauchy-approximation-Metric-Space
                ( M)
                ( x)
                ( ε⁺)
                ( 1/n'))))
```

### If the modulated Cauchy sequence associated with a Cauchy approximation has a limit, the approximation has the same limit

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  (x : cauchy-approximation-Metric-Space M)
  (lim : type-Metric-Space M)
  where

  abstract
    is-limit-cauchy-approximation-limit-modulated-cauchy-sequence-cauchy-approximation-Metric-Space :
      is-limit-modulated-cauchy-sequence-Metric-Space
        ( M)
        ( modulated-cauchy-sequence-cauchy-approximation-Metric-Space M x)
        ( lim) →
      is-limit-cauchy-approximation-Metric-Space M x lim
    is-limit-cauchy-approximation-limit-modulated-cauchy-sequence-cauchy-approximation-Metric-Space =
      rec-trunc-Prop
        ( is-limit-cauchy-approximation-prop-Metric-Space M x lim)
        ( is-limit-cauchy-approximation-limit-modulus-modulated-cauchy-sequence-cauchy-approximation-Metric-Space
          ( M)
          ( x)
          ( lim))
```
