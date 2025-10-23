# Cauchy approximations in metric spaces

```agda
module metric-spaces.cauchy-approximations-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.constant-maps
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import metric-spaces.cartesian-products-metric-spaces
open import metric-spaces.cauchy-approximations-pseudometric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.short-functions-metric-spaces
```

</details>

## Idea

A
{{#concept "Cauchy approximation" Disambiguation="in a metric space" Agda=is-cauchy-approximation-Metric-Space}}
in a [metric space](metric-spaces.metric-spaces.md) `A` is a
[Cauchy approximation](metric-spaces.cauchy-approximations-pseudometric-spaces.md)
in its underlying [pseudometric space](metric-spaces.pseudometric-spaces.md): a
map `f` from [`ℚ⁺`](elementary-number-theory.positive-rational-numbers.md) to
the carrier type of `A` such that for all positive rationals `ε` and `δ`, `f ε`
and `f δ` are in a
(`ε + δ`)-[neighborhood](metric-spaces.rational-neighborhood-relations.md),
i.e., the distance between `f ε` and `f δ` is bounded by `ε + δ`.

## Definitions

### Cauchy approximations in metric spaces

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  where

  is-cauchy-approximation-prop-Metric-Space :
    (ℚ⁺ → type-Metric-Space A) → Prop l2
  is-cauchy-approximation-prop-Metric-Space =
    is-cauchy-approximation-prop-Pseudometric-Space
      ( pseudometric-Metric-Space A)

  is-cauchy-approximation-Metric-Space :
    (ℚ⁺ → type-Metric-Space A) → UU l2
  is-cauchy-approximation-Metric-Space =
    type-Prop ∘ is-cauchy-approximation-prop-Metric-Space

  cauchy-approximation-Metric-Space : UU (l1 ⊔ l2)
  cauchy-approximation-Metric-Space =
    type-subtype is-cauchy-approximation-prop-Metric-Space
```

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  (f : cauchy-approximation-Metric-Space A)
  where

  map-cauchy-approximation-Metric-Space :
    ℚ⁺ → type-Metric-Space A
  map-cauchy-approximation-Metric-Space =
    map-cauchy-approximation-Pseudometric-Space
      ( pseudometric-Metric-Space A)
      ( f)

  is-cauchy-approximation-map-cauchy-approximation-Metric-Space :
    (ε δ : ℚ⁺) →
    neighborhood-Metric-Space
      ( A)
      ( ε +ℚ⁺ δ)
      ( map-cauchy-approximation-Metric-Space ε)
      ( map-cauchy-approximation-Metric-Space δ)
  is-cauchy-approximation-map-cauchy-approximation-Metric-Space =
    is-cauchy-approximation-map-cauchy-approximation-Pseudometric-Space
      ( pseudometric-Metric-Space A)
      ( f)
```

## Properties

### Constant maps in metric spaces are Cauchy approximations

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  (x : type-Metric-Space A)
  where

  const-cauchy-approximation-Metric-Space :
    cauchy-approximation-Metric-Space A
  const-cauchy-approximation-Metric-Space =
    const-cauchy-approximation-Pseudometric-Space
      ( pseudometric-Metric-Space A)
      ( x)
```

### The action of short maps on Cauchy approximations

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l1' l2')
  (f : short-function-Metric-Space A B)
  where

  map-short-function-cauchy-approximation-Metric-Space :
    cauchy-approximation-Metric-Space A →
    cauchy-approximation-Metric-Space B
  map-short-function-cauchy-approximation-Metric-Space =
    map-short-function-cauchy-approximation-Pseudometric-Space
      ( pseudometric-Metric-Space A)
      ( pseudometric-Metric-Space B)
      ( f)

module _
  {l1 l2 : Level}
  (A : Metric-Space l1 l2)
  where

  eq-id-map-short-function-cauchy-approximation-Metric-Space :
    map-short-function-cauchy-approximation-Metric-Space
      ( A)
      ( A)
      ( short-id-Metric-Space A) ＝
    id
  eq-id-map-short-function-cauchy-approximation-Metric-Space = refl

module _
  {l1a l2a l1b l2b l1c l2c : Level}
  (A : Metric-Space l1a l2a)
  (B : Metric-Space l1b l2b)
  (C : Metric-Space l1c l2c)
  (g : short-function-Metric-Space B C)
  (f : short-function-Metric-Space A B)
  where

  eq-comp-map-short-function-cauchy-approximation-Metric-Space :
    ( map-short-function-cauchy-approximation-Metric-Space B C g ∘
      map-short-function-cauchy-approximation-Metric-Space A B f) ＝
    ( map-short-function-cauchy-approximation-Metric-Space A C
      (comp-short-function-Metric-Space A B C g f))
  eq-comp-map-short-function-cauchy-approximation-Metric-Space = refl
```

### Homotopic Cauchy approximations are equal

```agda
module _
  { l1 l2 : Level} (A : Metric-Space l1 l2)
  { f g : cauchy-approximation-Metric-Space A}
  ( f~g :
    map-cauchy-approximation-Metric-Space A f ~
    map-cauchy-approximation-Metric-Space A g)
  where

  eq-htpy-cauchy-approximation-Metric-Space : f ＝ g
  eq-htpy-cauchy-approximation-Metric-Space =
    eq-htpy-cauchy-approximation-Pseudometric-Space
      ( pseudometric-Metric-Space A)
      ( f~g)
```

## References

Our definition of Cauchy approximation follows Definition 4.5.5 of
{{#cite Booij20PhD}} and Definition 11.2.10 of {{#cite UF13}}.

{{#bibliography}}
