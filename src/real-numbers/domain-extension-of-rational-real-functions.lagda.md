# Domain extension of rational real functions

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.domain-extension-of-rational-real-functions where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.rational-numbers

open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.isometries-metric-spaces
open import metric-spaces.metric-space-of-rational-numbers

open import real-numbers.dedekind-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.raising-universe-levels-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-real-numbers
```

</details>

## Idea

A [real](real-numbers.dedekind-real-numbers.md) function `g : ℝ → ℝ` is an
{{#concept "extension" Disambiguation="of rational real functions" Agda-is-extension-rational-function-ℝ}}
of a [rational](elementary-number-theory.rational-numbers.md) function
`f : ℚ → ℝ` if `g ∘ real-ℚ ~ f`.

## Definitions

### The property of being an extension of a rational real function

```agda
module _
  {l : Level}
  (f : ℚ → ℝ l) {l1 l2 : Level} (g : ℝ l1 → ℝ l2)
  where

  is-extension-rational-function-ℝ : UU (l ⊔ l2)
  is-extension-rational-function-ℝ =
    (q : ℚ) → sim-ℝ (g (raise-real-ℚ l1 q)) (f q)

  opaque
    unfolding sim-ℝ

    is-prop-is-extension-rational-function-ℝ :
      is-prop is-extension-rational-function-ℝ
    is-prop-is-extension-rational-function-ℝ =
      is-prop-Π
        ( λ q → is-prop-type-Prop (sim-prop-ℝ (g (raise-real-ℚ l1 q)) (f q)))

  is-extension-prop-rational-function-ℝ : Prop (l ⊔ l2)
  is-extension-prop-rational-function-ℝ =
    is-extension-rational-function-ℝ ,
    is-prop-is-extension-rational-function-ℝ
```

### The type of extensions of rational real functions

```agda
module _
  {l : Level} (f : ℚ → ℝ l) (l1 l2 : Level)
  where

  extension-rational-function-ℝ : UU (l ⊔ lsuc l1 ⊔ lsuc l2)
  extension-rational-function-ℝ =
    type-subtype (is-extension-prop-rational-function-ℝ f {l1} {l2})

  map-extension-rational-function-ℝ :
    extension-rational-function-ℝ → ℝ l1 → ℝ l2
  map-extension-rational-function-ℝ = pr1

  is-extention-map-extension-rational-function-ℝ :
    (H : extension-rational-function-ℝ) →
    is-extension-rational-function-ℝ f (map-extension-rational-function-ℝ H)
  is-extention-map-extension-rational-function-ℝ = pr2
```

## Properties

### If the extension of a rational real function is an isometry, so is the function

```agda
module _
  {l : Level}
  (f : ℚ → ℝ l) {l1 l2 : Level} (g : ℝ l1 → ℝ l2)
  (H : is-extension-rational-function-ℝ f g)
  where

  is-isometry-is-isometry-is-extension-rational-function-ℝ :
    is-isometry-Metric-Space
      ( metric-space-leq-ℝ l1)
      ( metric-space-leq-ℝ l2)
      ( g) →
    is-isometry-Metric-Space
      ( metric-space-leq-ℚ)
      ( metric-space-leq-ℝ l)
      ( f)
  is-isometry-is-isometry-is-extension-rational-function-ℝ I d x y =
    ( λ N →
      preserves-neighborhood-sim-ℝ
      ( d)
      ( g (raise-real-ℚ l1 x))
      ( g (raise-real-ℚ l1 y))
      ( f x)
      ( f y)
      ( H x)
      ( H y)
      ( forward-implication
        ( is-isometry-map-isometry-Metric-Space
          ( metric-space-leq-ℚ)
          ( metric-space-leq-ℝ l2)
          ( comp-isometry-Metric-Space
            ( metric-space-leq-ℚ)
            ( metric-space-leq-ℝ l1)
            ( metric-space-leq-ℝ l2)
            ( g , I)
            ( isometry-metric-space-leq-raise-real-ℚ l1))
          ( d)
          ( x)
          ( y))
          ( N))) ,
    ( λ N →
      backward-implication
        ( is-isometry-map-isometry-Metric-Space
          ( metric-space-leq-ℚ)
          ( metric-space-leq-ℝ l2)
          ( comp-isometry-Metric-Space
            ( metric-space-leq-ℚ)
            ( metric-space-leq-ℝ l1)
            ( metric-space-leq-ℝ l2)
            ( g , I)
            ( isometry-metric-space-leq-raise-real-ℚ l1))
          ( d)
          ( x)
          ( y))
          ( preserves-neighborhood-sim-ℝ
            ( d)
            ( f x)
            ( f y)
            ( g (raise-real-ℚ l1 x))
            ( g (raise-real-ℚ l1 y))
            ( symmetric-sim-ℝ (g (raise-real-ℚ l1 x)) (f x) (H x))
            ( symmetric-sim-ℝ (g (raise-real-ℚ l1 y)) (f y) (H y))
            ( N)))
```
