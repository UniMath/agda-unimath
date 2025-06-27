# Cauchy approximations in metric spaces (WIP)

```agda
module metric-spaces.cauchy-approximations-metric-spaces-WIP where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.constant-maps
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import metric-spaces.metric-spaces-WIP
open import metric-spaces.short-functions-metric-spaces-WIP
```

</details>

## Idea

A
{{#concept "Cauchy approximation" Disambiguation="in a metric space" Agda=is-cauchy-approximation-Metric-Space-WIP}}
in a [metric space](metric-spaces.metric-spaces.md) `A` is a map `f` from
[`ℚ⁺`](elementary-number-theory.positive-rational-numbers.md) to its carrier
type such that for all `(ε δ : ℚ⁺)`, `f ε` and `f δ` are in a
(`ε + δ`)-[neighborhood](metric-spaces.premetric-structures.md), i.e. the
distance between `f ε` and `f δ` is bounded by `ε + δ`.

## Definitions

### Cauchy approximations in metric spaces

```agda
module _
  {l1 l2 : Level} (A : Metric-Space-WIP l1 l2)
  where

  is-cauchy-approximation-prop-Metric-Space-WIP :
    (ℚ⁺ → type-Metric-Space-WIP A) → Prop l2
  is-cauchy-approximation-prop-Metric-Space-WIP f =
    Π-Prop
      ( ℚ⁺)
      ( λ ε →
        Π-Prop
          ( ℚ⁺)
          ( λ δ →
            neighborhood-prop-Metric-Space-WIP A (ε +ℚ⁺ δ) (f ε) (f δ)))

  is-cauchy-approximation-Metric-Space-WIP :
    (ℚ⁺ → type-Metric-Space-WIP A) → UU l2
  is-cauchy-approximation-Metric-Space-WIP =
    type-Prop ∘ is-cauchy-approximation-prop-Metric-Space-WIP

  cauchy-approximation-Metric-Space-WIP : UU (l1 ⊔ l2)
  cauchy-approximation-Metric-Space-WIP =
    type-subtype is-cauchy-approximation-prop-Metric-Space-WIP
```

```agda
module _
  {l1 l2 : Level} (A : Metric-Space-WIP l1 l2)
  (f : cauchy-approximation-Metric-Space-WIP A)
  where

  map-cauchy-approximation-Metric-Space-WIP :
    ℚ⁺ → type-Metric-Space-WIP A
  map-cauchy-approximation-Metric-Space-WIP = pr1 f

  is-cauchy-approximation-map-cauchy-approximation-Metric-Space-WIP :
    (ε δ : ℚ⁺) →
    neighborhood-Metric-Space-WIP
      ( A)
      ( ε +ℚ⁺ δ)
      ( map-cauchy-approximation-Metric-Space-WIP ε)
      ( map-cauchy-approximation-Metric-Space-WIP δ)
  is-cauchy-approximation-map-cauchy-approximation-Metric-Space-WIP = pr2 f
```

## Properties

### Constant maps in metric spaces are Cauchy approximations

```agda
module _
  {l1 l2 : Level} (A : Metric-Space-WIP l1 l2)
  (x : type-Metric-Space-WIP A)
  where

  const-cauchy-approximation-Metric-Space-WIP :
    cauchy-approximation-Metric-Space-WIP A
  const-cauchy-approximation-Metric-Space-WIP =
    (const ℚ⁺ x) , (λ ε δ → refl-neighborhood-Metric-Space-WIP A (ε +ℚ⁺ δ) x)
```

### Short maps between metric spaces are functorial on Cauchy approximations

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space-WIP l1 l2) (B : Metric-Space-WIP l1' l2')
  (f : short-function-Metric-Space-WIP A B)
  where

  map-short-function-cauchy-approximation-Metric-Space-WIP :
    cauchy-approximation-Metric-Space-WIP A →
    cauchy-approximation-Metric-Space-WIP B
  map-short-function-cauchy-approximation-Metric-Space-WIP (u , H) =
    ( map-short-function-Metric-Space-WIP A B f ∘ u) ,
    ( λ ε δ →
      is-short-map-short-function-Metric-Space-WIP
      ( A)
      ( B)
      ( f)
      ( ε +ℚ⁺ δ)
      ( u ε)
      ( u δ)
      ( H ε δ))

module _
  {l1 l2 : Level}
  (A : Metric-Space-WIP l1 l2)
  where

  eq-id-map-short-function-cauchy-approximation-Metric-Space-WIP :
    map-short-function-cauchy-approximation-Metric-Space-WIP
      ( A)
      ( A)
      ( short-id-Metric-Space-WIP A) ＝
    id
  eq-id-map-short-function-cauchy-approximation-Metric-Space-WIP = refl

module _
  {l1a l2a l1b l2b l1c l2c : Level}
  (A : Metric-Space-WIP l1a l2a)
  (B : Metric-Space-WIP l1b l2b)
  (C : Metric-Space-WIP l1c l2c)
  (g : short-function-Metric-Space-WIP B C)
  (f : short-function-Metric-Space-WIP A B)
  where

  eq-comp-map-short-function-cauchy-approximation-Metric-Space-WIP :
    ( map-short-function-cauchy-approximation-Metric-Space-WIP B C g ∘
      map-short-function-cauchy-approximation-Metric-Space-WIP A B f) ＝
    ( map-short-function-cauchy-approximation-Metric-Space-WIP A C
      (comp-short-function-Metric-Space-WIP A B C g f))
  eq-comp-map-short-function-cauchy-approximation-Metric-Space-WIP = refl
```

## References

Our definition of Cauchy approximation follows Definition 4.5.5 of
{{#cite Booij20PhD}} and Definition 11.2.10 of {{#cite UF13}}.

{{#bibliography}}
