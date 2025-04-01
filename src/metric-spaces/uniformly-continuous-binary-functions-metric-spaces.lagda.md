# Uniformly continuous binary functions between metric spaces

```agda
module metric-spaces.uniformly-continuous-binary-functions-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.minimum-rational-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.universe-levels

open import metric-spaces.continuous-functions-metric-spaces
open import metric-spaces.functions-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.products-metric-spaces
open import metric-spaces.short-functions-metric-spaces
open import metric-spaces.uniformly-continuous-functions-metric-spaces
```

</details>

## Idea

A [binary function](metric-spaces.functions-metric-spaces.md) `f` from
[metric spaces](metric-spaces.metric-spaces.md) `X` and `Y` to `Z` is
{{#concept "uniformly continuous" Disambiguation="binary function between metric spaces" WDID=Q741865 WD="uniform continuity" Agda=is-uniformly-continuous-binary-map-Metric-Space}}
if the induced map `ind-product f : X × Y → Z` is a uniformly continuous map
from the [product metric space](metric-spaces.products-metric-spaces.md) of `X`
and `Y` to `Z`.

## Definitions

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (X : Metric-Space l1 l2) (Y : Metric-Space l3 l4) (Z : Metric-Space l5 l6)
  (f : binary-map-type-Metric-Space X Y Z)
  where

  is-uniformly-continuous-binary-map-prop-Metric-Space :
    Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l6)
  is-uniformly-continuous-binary-map-prop-Metric-Space =
    is-uniformly-continuous-map-prop-Metric-Space
      ( product-Metric-Space X Y)
      ( Z)
      ( ind-product f)

  is-uniformly-continuous-binary-map-Metric-Space : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l6)
  is-uniformly-continuous-binary-map-Metric-Space =
    type-Prop is-uniformly-continuous-binary-map-prop-Metric-Space
```

## Properties

### The projection maps are uniformly continuous

```agda
module _
  {l1 l2 l3 l4 : Level}
  (X : Metric-Space l1 l2) (Y : Metric-Space l3 l4)
  where

  abstract
    is-uniformly-continuous-first-map-Metric-Space :
      is-uniformly-continuous-binary-map-Metric-Space X Y X (λ a b → a)
    is-uniformly-continuous-first-map-Metric-Space =
      is-uniformly-continuous-is-short-function-Metric-Space
        ( product-Metric-Space X Y)
        ( X)
        ( pr1)
        ( is-short-pr1-product-Metric-Space X Y)

    is-uniformly-continuous-second-map-Metric-Space :
      is-uniformly-continuous-binary-map-Metric-Space X Y Y (λ a b → b)
    is-uniformly-continuous-second-map-Metric-Space =
      is-uniformly-continuous-is-short-function-Metric-Space
        ( product-Metric-Space X Y)
        ( Y)
        ( pr2)
        ( is-short-pr2-product-Metric-Space X Y)
```

### Composing the arguments of a uniformly continuous binary function with uniformly continuous functions produces a uniformly continuous binary function

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l3 l4)
  (C : Metric-Space l5 l6) (D : Metric-Space l5 l6)
  (E : Metric-Space l9 l10)
  (f : binary-map-type-Metric-Space B D E)
  (ucf : is-uniformly-continuous-binary-map-Metric-Space B D E f)
  (g : map-type-Metric-Space A B)
  (ucg : is-uniformly-continuous-map-Metric-Space A B g)
  (h : map-type-Metric-Space C D)
  (uch : is-uniformly-continuous-map-Metric-Space C D h)
  where

  abstract
    comp-uniformly-continuous-binary-map-Metric-Space :
      is-uniformly-continuous-binary-map-Metric-Space A C E
        ( λ a c → f (g a) (h c))
    comp-uniformly-continuous-binary-map-Metric-Space =
      let
        open
          do-syntax-trunc-Prop
            ( is-uniformly-continuous-binary-map-prop-Metric-Space
              ( A)
              ( C)
              ( E)
              ( λ a c → f (g a) (h c)))
      in do
        mf , is-muc-mf ← ucf
        mg , is-muc-mg ← ucg
        mh , is-muc-mh ← uch
        intro-exists
          ( λ ε → min-ℚ⁺ (mg (mf ε)) (mh (mf ε)))
          ( λ (a , c) ε (a' , c') (a~a' , c~c') →
            is-muc-mf
              ( g a , h c)
              ( ε)
              ( g a' , h c')
              ( is-muc-mg
                ( a)
                ( mf ε)
                ( a')
                ( is-weakly-monotonic-structure-Metric-Space
                  ( A)
                  ( a)
                  ( a')
                  ( min-ℚ⁺ (mg (mf ε)) (mh (mf ε)))
                  ( mg (mf ε))
                  ( leq-left-min-ℚ
                    ( rational-ℚ⁺ (mg (mf ε)))
                    ( rational-ℚ⁺ (mh (mf ε))))
                  ( a~a')) ,
            is-muc-mh
              ( c)
              ( mf ε)
              ( c')
              ( is-weakly-monotonic-structure-Metric-Space
                ( C)
                ( c)
                ( c')
                ( min-ℚ⁺ (mg (mf ε)) (mh (mf ε)))
                ( mh (mf ε))
                ( leq-right-min-ℚ
                  ( rational-ℚ⁺ (mg (mf ε)))
                  ( rational-ℚ⁺ (mh (mf ε))))
                ( c~c'))))
```
