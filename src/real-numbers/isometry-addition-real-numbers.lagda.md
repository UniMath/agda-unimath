# The isometric addition of real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.isometry-addition-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.difference-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.diagonal-maps-cartesian-products-of-types
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.extensional-premetric-structures
open import metric-spaces.isometries-metric-spaces
open import metric-spaces.metric-space-functions-metric-spaces
open import metric-spaces.metric-space-of-rational-numbers
open import metric-spaces.metric-spaces
open import metric-spaces.metric-structures
open import metric-spaces.premetric-spaces
open import metric-spaces.premetric-structures
open import metric-spaces.pseudometric-structures
open import metric-spaces.reflexive-premetric-structures
open import metric-spaces.saturated-metric-spaces
open import metric-spaces.symmetric-premetric-structures
open import metric-spaces.triangular-premetric-structures

open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.raising-universe-levels-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.strict-inequality-real-numbers
```

</details>

## Idea

For any `a : ℝ l`, `add-ℝ a` is an isometry `ℝ → ℝ`. The map `x → add-ℝ x` is an
isometry `ℝ → (ℝ → ℝ)` (with the dependent product metric structure).

## Definitions

### Addition with a real number is an isometry `ℝ → ℝ`

```agda
module _
  {l1 l2 : Level} (x : ℝ l1)
  where

  is-isometry-left-add-ℝ :
    is-isometry-Metric-Space
      ( metric-space-leq-ℝ l2)
      ( metric-space-leq-ℝ (l1 ⊔ l2))
      ( add-ℝ x)
  is-isometry-left-add-ℝ d y z =
    ( λ Nyz →
      neighborhood-real-bound-each-leq-ℝ
        ( d)
        ( add-ℝ x y)
        ( add-ℝ x z)
        ( preserves-lower-neighborhood-leq-left-add-ℝ d x y z
          ( left-real-bound-neighborhood-leq-ℝ d y z Nyz))
        ( preserves-lower-neighborhood-leq-left-add-ℝ d x z y
          ( right-real-bound-neighborhood-leq-ℝ d y z Nyz))) ,
    ( λ Nxyz →
      neighborhood-real-bound-each-leq-ℝ d y z
        ( reflects-lower-neighborhood-leq-left-add-ℝ d x y z
          ( left-real-bound-neighborhood-leq-ℝ d (x +ℝ y) (x +ℝ z) Nxyz))
        ( reflects-lower-neighborhood-leq-left-add-ℝ d x z y
          ( right-real-bound-neighborhood-leq-ℝ d (x +ℝ y) (x +ℝ z) Nxyz)))

  isometry-left-add-ℝ :
    isometry-Metric-Space
      ( metric-space-leq-ℝ l2)
      ( metric-space-leq-ℝ (l1 ⊔ l2))
  isometry-left-add-ℝ = add-ℝ x , is-isometry-left-add-ℝ
```

### Addition is an isometry from `ℝ` to the metric space of isometries `ℝ → ℝ`

```agda
module _
  {l1 l2 : Level}
  where

  is-isometry-isometry-left-add-ℝ :
    is-isometry-Metric-Space
      ( metric-space-leq-ℝ l1)
      ( metric-space-isometry-Metric-Space
        ( metric-space-leq-ℝ l2)
        ( metric-space-leq-ℝ (l1 ⊔ l2)))
      ( isometry-left-add-ℝ)
  is-isometry-isometry-left-add-ℝ d x y =
    ( λ Nxy z →
      neighborhood-real-bound-each-leq-ℝ
        ( d)
        ( add-ℝ x z)
        ( add-ℝ y z)
        ( preserves-lower-neighborhood-leq-right-add-ℝ d z x y
          ( left-real-bound-neighborhood-leq-ℝ d x y Nxy))
        ( preserves-lower-neighborhood-leq-right-add-ℝ d z y x
          ( right-real-bound-neighborhood-leq-ℝ d x y Nxy))) ,
    ( λ Nxyz →
      neighborhood-real-bound-each-leq-ℝ d x y
        ( reflects-lower-neighborhood-leq-right-add-ℝ
          ( d)
          ( raise-ℝ l2 zero-ℝ)
          ( x)
          ( y)
          ( left-real-bound-neighborhood-leq-ℝ
            ( d)
            ( x +ℝ raise-ℝ l2 zero-ℝ)
            ( y +ℝ raise-ℝ l2 zero-ℝ)
            ( Nxyz (raise-ℝ l2 zero-ℝ))))
        ( reflects-lower-neighborhood-leq-right-add-ℝ
          ( d)
          ( raise-ℝ l2 zero-ℝ)
          ( y)
          ( x)
          ( right-real-bound-neighborhood-leq-ℝ
            ( d)
            ( x +ℝ raise-ℝ l2 zero-ℝ)
            ( y +ℝ raise-ℝ l2 zero-ℝ)
            ( Nxyz (raise-ℝ l2 zero-ℝ)))))

  isometry-add-ℝ :
    isometry-Metric-Space
      ( metric-space-leq-ℝ l1)
      ( metric-space-isometry-Metric-Space
        ( metric-space-leq-ℝ l2)
        ( metric-space-leq-ℝ (l1 ⊔ l2)))
  isometry-add-ℝ = isometry-left-add-ℝ , is-isometry-isometry-left-add-ℝ
```
