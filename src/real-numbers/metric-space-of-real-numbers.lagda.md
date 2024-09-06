# The metric space of real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.metric-space-of-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.difference-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.isometry-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.premetric-structures
open import metric-spaces.saturated-metric-space-of-rational-numbers
open import metric-spaces.saturated-metric-spaces

open import real-numbers.dedekind-real-numbers
open import real-numbers.rational-real-numbers
```

</details>

## Idea

The type of [real numbers](real-numbers.dedekind-real-numbers.md) equipped with
the [premetric](metric-spaces.premetric-structures.md) where `x y : ℝ` are
`d`-neighbours when for any `r : ℚ` the following two conditions hold:

- if `r + d` is in the lower cut of `y`, `r` is in the lower cut of `x`
- if `r + d` is in the lower cut of `x`, `r` is in the lower cut of `y`

is a [saturated metric space](metric-spaces.saturated-metric-spaces.md).

It is the
{{#concept "standard saturated metric space of real numbers" Agda=metric-space-leq-ℝ}}.

## Definitions

### The standard closed premetric on the real numbers

```agda
premetric-leq-ℝ : (l : Level) → Premetric l (ℝ l)
premetric-leq-ℝ l d x y =
  product-Prop
    ( Π-Prop
      ( ℚ)
      ( λ r →
        hom-Prop
          ( lower-cut-ℝ y (r +ℚ (rational-ℚ⁺ d)))
          ( lower-cut-ℝ x r)))
    ( Π-Prop
      ( ℚ)
      ( λ r →
        hom-Prop
          ( lower-cut-ℝ x (r +ℚ (rational-ℚ⁺ d)))
          ( lower-cut-ℝ y r)))
```

## Properties

### The standard premetric on the real numbers is a metric structure

```agda
is-reflexive-premetric-leq-ℝ :
  {l : Level} → is-reflexive-Premetric (premetric-leq-ℝ l)
is-reflexive-premetric-leq-ℝ d x = H , H
  where

  H : (r : ℚ) → is-in-lower-cut-ℝ x (r +ℚ rational-ℚ⁺ d) → is-in-lower-cut-ℝ x r
  H r = le-lower-cut-ℝ x r (r +ℚ rational-ℚ⁺ d) (le-right-add-rational-ℚ⁺ r d)

is-symmetric-premetric-leq-ℝ :
  {l : Level} → is-symmetric-Premetric (premetric-leq-ℝ l)
is-symmetric-premetric-leq-ℝ d x y (H , K) = (K , H)

is-tight-premetric-leq-ℝ : {l : Level} → is-tight-Premetric (premetric-leq-ℝ l)
is-tight-premetric-leq-ℝ x y H =
  eq-eq-lower-cut-ℝ
    ( x)
    ( y)
    ( antisymmetric-leq-subtype
      ( lower-cut-ℝ x)
      ( lower-cut-ℝ y)
      ( λ r Lxr →
        elim-exists
          ( lower-cut-ℝ y r)
          ( λ s (r<s , Lxs) →
            pr2
              ( H (positive-diff-le-ℚ r s r<s))
              ( r)
              ( inv-tr
                ( λ u → is-in-lower-cut-ℝ x u)
                ( right-law-positive-diff-le-ℚ r s r<s)
                ( Lxs)))
          ( forward-implication (is-rounded-lower-cut-ℝ x r) Lxr))
      ( λ r Lyr →
        elim-exists
          ( lower-cut-ℝ x r)
          ( λ s (r<s , Lys) →
            pr1
              ( H (positive-diff-le-ℚ r s r<s))
              ( r)
              ( inv-tr
                ( λ u → is-in-lower-cut-ℝ y u)
                ( right-law-positive-diff-le-ℚ r s r<s)
                ( Lys)))
          ( forward-implication (is-rounded-lower-cut-ℝ y r) Lyr)))

is-local-premetric-leq-ℝ : {l : Level} → is-local-Premetric (premetric-leq-ℝ l)
is-local-premetric-leq-ℝ {l} =
  is-local-is-tight-Premetric
    ( premetric-leq-ℝ l)
    ( is-tight-premetric-leq-ℝ)

is-triangular-premetric-leq-ℝ :
  {l : Level} → is-triangular-Premetric (premetric-leq-ℝ l)
pr1 (is-triangular-premetric-leq-ℝ x y z dxy dyz Hyz Hxy) r =
  pr1 Hxy r ∘
  pr1 Hyz (r +ℚ rational-ℚ⁺ dxy) ∘
  inv-tr
    ( is-in-lower-cut-ℝ z)
    ( associative-add-ℚ r (rational-ℚ⁺ dxy) (rational-ℚ⁺ dyz))
pr2 (is-triangular-premetric-leq-ℝ x y z dxy dyz Hyz Hxy) r =
  pr2 Hyz r ∘
  pr2 Hxy (r +ℚ rational-ℚ⁺ dyz) ∘
  inv-tr
    ( is-in-lower-cut-ℝ x)
    ( associative-add-ℚ r (rational-ℚ⁺ dyz) (rational-ℚ⁺ dxy) ∙
      ap (add-ℚ r) (commutative-add-ℚ (rational-ℚ⁺ dyz) (rational-ℚ⁺ dxy)))
```

### The standard saturated metric space of real numbers

```agda
module _
  (l : Level)
  where

  metric-space-leq-ℝ : Metric-Space (lsuc l) l
  pr1 metric-space-leq-ℝ = ℝ l , premetric-leq-ℝ l
  pr2 metric-space-leq-ℝ =
    is-reflexive-premetric-leq-ℝ ,
    is-symmetric-premetric-leq-ℝ ,
    is-local-premetric-leq-ℝ ,
    is-triangular-premetric-leq-ℝ
```

## Properties

### The standard saturated metric space of real numbers is saturated

```agda
module _
  {l : Level}
  where

  is-saturated-metric-space-leq-ℝ :
    is-saturated-Metric-Space (metric-space-leq-ℝ l)
  is-saturated-metric-space-leq-ℝ ε x y H =
    ( λ r Lyr →
      elim-exists
        ( lower-cut-ℝ x r)
        ( λ r' (I' , Lyr') →
          pr1
            ( H (positive-diff-le-ℚ (r +ℚ rational-ℚ⁺ ε) r' I'))
            ( r)
            ( tr
              ( is-in-lower-cut-ℝ y)
              ( ( inv
                  ( right-law-positive-diff-le-ℚ
                    ( r +ℚ rational-ℚ⁺ ε)
                    ( r')
                    ( I'))) ∙
                ( associative-add-ℚ
                  ( r)
                  ( rational-ℚ⁺ ε)
                  ( r' -ℚ (r +ℚ rational-ℚ⁺ ε))))
              ( Lyr')))
        ( forward-implication
          ( is-rounded-lower-cut-ℝ y (r +ℚ rational-ℚ⁺ ε)) Lyr)) ,
    ( λ r Lxr →
      elim-exists
        ( lower-cut-ℝ y r)
        ( λ r' (I' , Lxr') →
          pr2
            ( H (positive-diff-le-ℚ (r +ℚ rational-ℚ⁺ ε) r' I'))
            ( r)
            ( tr
              ( is-in-lower-cut-ℝ x)
              ( ( inv
                  ( right-law-positive-diff-le-ℚ
                    ( r +ℚ rational-ℚ⁺ ε)
                    ( r')
                    ( I'))) ∙
                ( associative-add-ℚ
                  ( r)
                  ( rational-ℚ⁺ ε)
                  ( r' -ℚ (r +ℚ rational-ℚ⁺ ε))))
              ( Lxr')))
        ( forward-implication
          ( is-rounded-lower-cut-ℝ x (r +ℚ rational-ℚ⁺ ε)) Lxr))
```

### Tha canonical embedding from rational to real numbers is an isometry between metric spaces

```agda
is-isometry-metric-space-leq-real-ℚ :
  is-isometry-Metric-Space
    ( metric-space-leq-ℚ)
    ( metric-space-leq-ℝ lzero)
    ( real-ℚ)
is-isometry-metric-space-leq-real-ℚ d x y =
  pair
    ( map-product
      ( le-le-add-positive-leq-add-positive-ℚ x y d)
      ( le-le-add-positive-leq-add-positive-ℚ y x d))
    ( map-product
      ( leq-add-positive-le-le-add-positive-ℚ x y d)
      ( leq-add-positive-le-le-add-positive-ℚ y x d))
```
