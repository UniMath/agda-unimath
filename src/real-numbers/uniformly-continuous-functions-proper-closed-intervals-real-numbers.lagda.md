# Uniformly continuous functions on proper closed intervals of real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.uniformly-continuous-functions-proper-closed-intervals-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.images
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import metric-spaces.metric-spaces
open import metric-spaces.uniformly-continuous-functions-metric-spaces

open import real-numbers.apartness-real-numbers
open import real-numbers.closed-intervals-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.proper-closed-intervals-real-numbers
open import real-numbers.subsets-real-numbers
```

</details>

## Idea

A
{{#concept "uniformly continuous function" Disambiguation="from a proper closed interval in ℝ to ℝ" Agda=ucont-map-proper-closed-interval-ℝ}}
from a
[proper closed interval](real-numbers.proper-closed-intervals-real-numbers.md)
in the [real numbers](real-numbers.dedekind-real-numbers.md) to the real numbers
always has its [image](foundation.images.md) contained in a
[closed interval](real-numbers.closed-intervals-real-numbers.md).

## Definition

```agda
is-ucont-prop-map-proper-closed-interval-ℝ :
  {l1 l2 l3 l4 : Level} ([a,b] : proper-closed-interval-ℝ l3 l4) →
  (type-proper-closed-interval-ℝ l1 [a,b] → ℝ l2) →
  Prop (lsuc l1 ⊔ l2 ⊔ l3 ⊔ l4)
is-ucont-prop-map-proper-closed-interval-ℝ {l1} {l2} [a,b] =
  is-uniformly-continuous-prop-function-Metric-Space
    ( metric-space-proper-closed-interval-ℝ l1 [a,b])
    ( metric-space-ℝ l2)

is-ucont-map-proper-closed-interval-ℝ :
  {l1 l2 l3 l4 : Level} ([a,b] : proper-closed-interval-ℝ l3 l4) →
  (type-proper-closed-interval-ℝ l1 [a,b] → ℝ l2) →
  UU (lsuc l1 ⊔ l2 ⊔ l3 ⊔ l4)
is-ucont-map-proper-closed-interval-ℝ [a,b] f =
  type-Prop
    ( is-ucont-prop-map-proper-closed-interval-ℝ [a,b] f)

ucont-map-proper-closed-interval-ℝ :
  (l1 l2 : Level) {l3 l4 : Level} →
  proper-closed-interval-ℝ l3 l4 → UU (lsuc (l1 ⊔ l2) ⊔ l3 ⊔ l4)
ucont-map-proper-closed-interval-ℝ l1 l2 [a,b] =
  uniformly-continuous-function-Metric-Space
    ( metric-space-proper-closed-interval-ℝ l1 [a,b])
    ( metric-space-ℝ l2)
```

## Properties

### The image of a uniformly continuous function on a proper closed interval

```agda
module _
  {l1 l2 : Level}
  ([a,b] : proper-closed-interval-ℝ l1 l1)
  (f : ucont-map-proper-closed-interval-ℝ l1 l2 [a,b])
  where

  map-ucont-map-proper-closed-interval-ℝ :
    type-proper-closed-interval-ℝ l1 [a,b] → ℝ l2
  map-ucont-map-proper-closed-interval-ℝ = pr1 f

  is-ucont-map-ucont-map-proper-closed-interval-ℝ :
    is-ucont-map-proper-closed-interval-ℝ
      ( [a,b])
      ( map-ucont-map-proper-closed-interval-ℝ)
  is-ucont-map-ucont-map-proper-closed-interval-ℝ =
    pr2 f

  subset-im-ucont-map-proper-closed-interval-ℝ :
    subset-ℝ (lsuc (l1 ⊔ l2)) l2
  subset-im-ucont-map-proper-closed-interval-ℝ =
    subtype-im map-ucont-map-proper-closed-interval-ℝ

  subspace-im-ucont-map-proper-closed-interval-ℝ :
    Metric-Space (lsuc (l1 ⊔ l2)) l2
  subspace-im-ucont-map-proper-closed-interval-ℝ =
    metric-space-subset-ℝ
      ( subset-im-ucont-map-proper-closed-interval-ℝ)
```

### To show a function on a proper closed interval of real numbers is uniformly continuous, it suffices to exhibit a modulus that applies when its arguments are apart

```agda
module _
  {l1 l2 l3 l4 : Level}
  ([a,b] : proper-closed-interval-ℝ l1 l2)
  (f : type-proper-closed-interval-ℝ (l1 ⊔ l2 ⊔ l3) [a,b] → ℝ l4)
  (μ : ℚ⁺ → ℚ⁺)
  (H :
    (ε : ℚ⁺) (x y : type-proper-closed-interval-ℝ (l1 ⊔ l2 ⊔ l3) [a,b]) →
    apart-ℝ (pr1 x) (pr1 y) →
    neighborhood-ℝ _ (μ ε) (pr1 x) (pr1 y) →
    neighborhood-ℝ _ ε (f x) (f y))
  where

  abstract
    is-ucont-map-modulus-apart-map-proper-closed-interval-ℝ :
      is-ucont-map-proper-closed-interval-ℝ [a,b] f
    is-ucont-map-modulus-apart-map-proper-closed-interval-ℝ =
      intro-exists
        ( μ ∘ modulus-le-double-le-ℚ⁺)
        ( λ x ε y Nxy →
          let
            (ε' , ε'+ε'<ε) = bound-double-le-ℚ⁺ ε
            open do-syntax-trunc-Prop (neighborhood-prop-ℝ l4 ε (f x) (f y))
          in do
            (z , z#x , z#y , Nεzx , Nεzy) ←
              exists-element-apart-from-both-in-neighborhood-proper-closed-interval-ℝ
                ( l3)
                ( [a,b])
                ( x)
                ( y)
                ( μ ε')
                ( Nxy)
            weakly-monotonic-neighborhood-ℝ
              ( f x)
              ( f y)
              ( ε' +ℚ⁺ ε')
              ( ε)
              ( leq-le-ℚ ε'+ε'<ε)
              ( is-triangular-neighborhood-ℝ
                ( f x)
                ( f z)
                ( f y)
                ( ε')
                ( ε')
                ( H ε' z y z#y Nεzy)
                ( H
                  ( ε')
                  ( x)
                  ( z)
                  ( symmetric-apart-ℝ z#x)
                  ( is-symmetric-neighborhood-ℝ (μ ε') (pr1 z) (pr1 x) Nεzx))))
```
