# Approximations in metric spaces

```agda
module metric-spaces.approximations-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.full-subtypes
open import foundation.function-types
open import foundation.images
open import foundation.images-subtypes
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.unions-subtypes
open import foundation.universe-levels

open import metric-spaces.equality-of-metric-spaces
open import metric-spaces.functions-metric-spaces
open import metric-spaces.images-isometries-metric-spaces
open import metric-spaces.images-metric-spaces
open import metric-spaces.images-short-functions-metric-spaces
open import metric-spaces.images-uniformly-continuous-functions-metric-spaces
open import metric-spaces.isometries-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.short-functions-metric-spaces
open import metric-spaces.subspaces-metric-spaces
open import metric-spaces.uniformly-continuous-functions-metric-spaces
```

</details>

## Idea

For an `ε : ℚ⁺`, an
`ε`-{{#concept "approximation" disambiguation="of a metric space" Agda=approximation-Metric-Space}}
of a [metric space](metric-spaces.metric-spaces.md) `X` is a
[subset](foundation.subtypes.md) `S` of `X` such that every point in `X` is in
an `ε`-neighborhood of some `s ∈ S`.

This terminology is taken from {{#cite BV06}} section 2.2.

A [finitely enumerable](univalent-combinatorics.finitely-enumerable-types.md)
`ε`-approximation is called an [`ε`-net](metric-spaces.nets-metric-spaces.md).

## Definitions

```agda
module _
  {l1 l2 l3 : Level} (X : Metric-Space l1 l2) (ε : ℚ⁺)
  (S : subset-Metric-Space l3 X)
  where

  is-approximation-prop-Metric-Space : Prop (l1 ⊔ l2 ⊔ l3)
  is-approximation-prop-Metric-Space =
    is-full-subtype-Prop
      ( union-family-of-subtypes
        { I = type-subtype S}
        ( λ (s , s∈S) → neighborhood-prop-Metric-Space X ε s))

  is-approximation-Metric-Space : UU (l1 ⊔ l2 ⊔ l3)
  is-approximation-Metric-Space =
    type-Prop is-approximation-prop-Metric-Space

approximation-Metric-Space :
  {l1 l2 : Level} (l3 : Level) (X : Metric-Space l1 l2) (ε : ℚ⁺) →
  UU (l1 ⊔ l2 ⊔ lsuc l3)
approximation-Metric-Space l3 X ε =
  type-subtype (is-approximation-prop-Metric-Space {l3 = l3} X ε)

module _
  {l1 l2 l3 : Level} (X : Metric-Space l1 l2) (ε : ℚ⁺)
  (S : approximation-Metric-Space l3 X ε)
  where

  subset-approximation-Metric-Space : subset-Metric-Space l3 X
  subset-approximation-Metric-Space = pr1 S

  type-approximation-Metric-Space : UU (l1 ⊔ l3)
  type-approximation-Metric-Space =
    type-subtype subset-approximation-Metric-Space

  is-approximation-approximation-Metric-Space :
    is-approximation-Metric-Space X ε subset-approximation-Metric-Space
  is-approximation-approximation-Metric-Space = pr2 S
```

## Properties

### If `μ` is a modulus of uniform continuity for `f : X → Y` and `A` is a `(μ ε)`-approximation of `X`, then `im f A` is an `ε`-approximation of `im f X`

```agda
module _
  {l1 l2 l3 l4 l5 : Level} (X : Metric-Space l1 l2) (Y : Metric-Space l3 l4)
  (f : type-function-Metric-Space X Y) {μ : ℚ⁺ → ℚ⁺}
  (is-modulus-ucont-f-μ :
    is-modulus-of-uniform-continuity-function-Metric-Space X Y f μ)
  (ε : ℚ⁺) (A : approximation-Metric-Space l5 X (μ ε))
  where

  abstract
    is-approximation-im-uniformly-continuous-function-approximation-Metric-Space :
      is-approximation-Metric-Space
        ( im-Metric-Space X Y f)
        ( ε)
        ( im-subtype
          ( map-unit-im f)
          ( subset-approximation-Metric-Space X (μ ε) A))
    is-approximation-im-uniformly-continuous-function-approximation-Metric-Space
      (y , ∃x:fx=y) =
        let
          open
            do-syntax-trunc-Prop
              ( ∃ _ (λ z → neighborhood-prop-Metric-Space Y ε (pr1 (pr1 z)) y))
        in do
          (x , fx=y) ← ∃x:fx=y
          ((a , a∈A) , Nμεax) ←
            is-approximation-approximation-Metric-Space X (μ ε) A x
          intro-exists
            ( map-unit-im
              ( map-unit-im f ∘
                inclusion-subtype
                  ( subset-approximation-Metric-Space X (μ ε) A))
              ( a , a∈A))
            ( tr
              ( neighborhood-Metric-Space Y ε (f a))
              ( fx=y)
              ( is-modulus-ucont-f-μ a ε x Nμεax))

  approximation-im-uniformly-continuous-function-approximation-Metric-Space :
    approximation-Metric-Space (l1 ⊔ l3 ⊔ l5) (im-Metric-Space X Y f) ε
  approximation-im-uniformly-continuous-function-approximation-Metric-Space =
    ( im-subtype (map-unit-im f) (subset-approximation-Metric-Space X (μ ε) A) ,
      is-approximation-im-uniformly-continuous-function-approximation-Metric-Space)
```

### If `f : X → Y` is a short function and `A` is an `ε`-approximation of `X`, then `im f A` is an `ε`-approximation of `im f X`

```agda
module _
  {l1 l2 l3 l4 l5 : Level} (X : Metric-Space l1 l2) (Y : Metric-Space l3 l4)
  (f : short-function-Metric-Space X Y)
  (ε : ℚ⁺) (A : approximation-Metric-Space l5 X ε)
  where

  approximation-im-short-function-approximation-Metric-Space :
    approximation-Metric-Space
      ( l1 ⊔ l3 ⊔ l5)
      ( im-short-function-Metric-Space X Y f)
      ( ε)
  approximation-im-short-function-approximation-Metric-Space =
    approximation-im-uniformly-continuous-function-approximation-Metric-Space
      ( X)
      ( Y)
      ( map-short-function-Metric-Space X Y f)
      ( id-is-modulus-of-uniform-continuity-is-short-function-Metric-Space
        ( X)
        ( Y)
        ( map-short-function-Metric-Space X Y f)
        ( is-short-map-short-function-Metric-Space X Y f))
      ( ε)
      ( A)
```

### If `f : X → Y` is an isometry and `A` is an `ε`-approximation of `X`, then `im f A` is an `ε`-approximation of `im f X`

```agda
module _
  {l1 l2 l3 l4 l5 : Level} (X : Metric-Space l1 l2) (Y : Metric-Space l3 l4)
  (f : isometry-Metric-Space X Y)
  (ε : ℚ⁺) (A : approximation-Metric-Space l5 X ε)
  where

  approximation-im-isometry-approximation-Metric-Space :
    approximation-Metric-Space
      ( l1 ⊔ l3 ⊔ l5)
      ( im-isometry-Metric-Space X Y f)
      ( ε)
  approximation-im-isometry-approximation-Metric-Space =
    approximation-im-short-function-approximation-Metric-Space X Y
      ( short-isometry-Metric-Space X Y f)
      ( ε)
      ( A)
```

### If `f : X ≃ Y` is an isometric equivalence and `A` is an `ε`-approximation of `X`, then `im f A` is an `ε`-approximation of `Y`

```agda
module _
  {l1 l2 l3 l4 l5 : Level} (X : Metric-Space l1 l2) (Y : Metric-Space l3 l4)
  (f : isometric-equiv-Metric-Space X Y)
  (ε : ℚ⁺) (A : approximation-Metric-Space l5 X ε)
  where

  abstract
    is-approximation-im-isometric-equiv-Metric-Space :
      is-approximation-Metric-Space
        ( Y)
        ( ε)
        ( im-subtype
          ( map-isometric-equiv-Metric-Space X Y f)
          ( subset-approximation-Metric-Space X ε A))
    is-approximation-im-isometric-equiv-Metric-Space y =
      let
        open
          do-syntax-trunc-Prop
            ( ∃ _ (λ z → neighborhood-prop-Metric-Space Y ε (pr1 z) y))
      in do
        let x = map-inv-isometric-equiv-Metric-Space X Y f y
        ((a , a∈A) , Nεax) ← is-approximation-approximation-Metric-Space X ε A x
        intro-exists
          ( map-unit-im
            ( map-isometric-equiv-Metric-Space X Y f ∘
              inclusion-subtype (subset-approximation-Metric-Space X ε A))
            ( a , a∈A))
          ( tr
            ( neighborhood-Metric-Space Y ε
              ( map-isometric-equiv-Metric-Space X Y f a))
            ( is-section-map-inv-equiv-Metric-Space X Y f y)
            ( forward-implication
              ( is-isometry-map-isometric-equiv-Metric-Space X Y f ε _ _)
              ( Nεax)))

  approximation-im-isometric-equiv-Metric-Space :
    approximation-Metric-Space (l1 ⊔ l3 ⊔ l5) Y ε
  approximation-im-isometric-equiv-Metric-Space =
    ( im-subtype
        ( map-isometric-equiv-Metric-Space X Y f)
        ( subset-approximation-Metric-Space X ε A) ,
      is-approximation-im-isometric-equiv-Metric-Space)
```

## References

{{#bibliography}}
