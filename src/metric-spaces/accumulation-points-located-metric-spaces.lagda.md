# Accumulation points in located metric spaces

```agda
module metric-spaces.accumulation-points-located-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.intersections-subtypes
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import lists.sequences

open import metric-spaces.apartness-located-metric-spaces
open import metric-spaces.closed-subsets-located-metric-spaces
open import metric-spaces.limits-of-sequences-metric-spaces
open import metric-spaces.located-metric-spaces
open import metric-spaces.subspaces-metric-spaces
```

</details>

## Idea

An
{{#concept "accumulation point" WDID=Q858223 WD="limit point" Disambiguation="of a metric space" Agda=accumulation-point-Metric-Space}}
of a subset `S` of a
[located metric space](metric-spaces.located-metric-spaces.md) `X` is a point
`x : X` such that there exists a [sequence](lists.sequences.md) `aₙ` of points
in `S` such that `x` is the
[limit](metric-spaces.limits-of-sequences-metric-spaces.md) of `aₙ`, and for
every `n`, `aₙ` is [apart](metric-spaces.apartness-located-metric-spaces.md)
from `x`.

## Definition

```agda
module _
  {l1 l2 l3 : Level}
  (X : Located-Metric-Space l1 l2)
  (S : subset-Located-Metric-Space l3 X)
  where

  is-accumulation-point-prop-subset-Located-Metric-Space :
    subset-Metric-Space (l1 ⊔ l2 ⊔ l3) (metric-space-Located-Metric-Space X)
  is-accumulation-point-prop-subset-Located-Metric-Space x =
    ∃ ( sequence (type-subtype S))
      ( λ a →
        Π-Prop ℕ (λ n → apart-prop-Located-Metric-Space X (pr1 (a n)) x) ∧
        is-limit-prop-sequence-Metric-Space
          ( metric-space-Located-Metric-Space X)
          ( pr1 ∘ a)
          ( x))

  is-accumulation-point-subset-Located-Metric-Space :
    type-Located-Metric-Space X → UU (l1 ⊔ l2 ⊔ l3)
  is-accumulation-point-subset-Located-Metric-Space x =
    type-Prop (is-accumulation-point-prop-subset-Located-Metric-Space x)

  accumulation-point-subset-Located-Metric-Space : UU (l1 ⊔ l2 ⊔ l3)
  accumulation-point-subset-Located-Metric-Space =
    type-subtype is-accumulation-point-prop-subset-Located-Metric-Space
```

## Properties

### A closed subset of a metric space contains all its accumulation points

```agda
module _
  {l1 l2 l3 : Level}
  (X : Located-Metric-Space l1 l2)
  (S : closed-subset-Located-Metric-Space l3 X)
  where

  is-in-closed-subset-is-accumulation-point-Located-Metric-Space :
    (x : type-Located-Metric-Space X) →
    is-accumulation-point-subset-Located-Metric-Space
      ( X)
      ( subset-closed-subset-Located-Metric-Space X S)
      ( x) →
    is-in-closed-subset-Located-Metric-Space X S x
  is-in-closed-subset-is-accumulation-point-Located-Metric-Space x is-acc-x =
    is-closed-subset-closed-subset-Located-Metric-Space
      ( X)
      ( S)
      ( x)
      ( λ ε →
        let
          open
            do-syntax-trunc-Prop
              ( ∃
                ( type-Located-Metric-Space X)
                ( λ y →
                  neighborhood-prop-Located-Metric-Space X ε x y ∧
                  subset-closed-subset-Located-Metric-Space X S y))
        in do
          (a , a#x , lim-a=x) ← is-acc-x
          (μ , is-mod-μ) ← lim-a=x
          let (y , y∈S) = a (μ ε)
          intro-exists
            ( y)
            ( symmetric-neighborhood-Located-Metric-Space X
                ( ε)
                ( y)
                ( x)
                ( is-mod-μ ε (μ ε) (refl-leq-ℕ (μ ε))) ,
              y∈S))
```
