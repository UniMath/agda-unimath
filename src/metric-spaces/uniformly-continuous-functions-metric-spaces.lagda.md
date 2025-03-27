# Uniformly continuous functions between metric spaces

```agda
module metric-spaces.uniformly-continuous-functions-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.inhabited-subtypes
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import metric-spaces.continuous-functions-metric-spaces
open import metric-spaces.functions-metric-spaces
open import metric-spaces.metric-spaces
```

</details>

## Idea

A [function](metric-spaces.functions-metric-spaces.md) `f` between
[metric spaces](metric-spaces.metric-spaces.md) `X` and `Y` is
{{#concept "uniformly continuous" Disambiguation="function between metric spaces" WDID=Q741865 WD="uniform continuity" Agda=is-uniformly-continuous-map-Metric-Space}}
if there exists a function `m : ℚ⁺ → ℚ⁺` such that for any `x : X`, whenever
`x'` is in an `m ε`-neighborhood of `x`, `f x'` is in an `ε`-neighborhood of
`f x`. The function `m` is called a modulus of uniform continuity of `f`.

## Definitions

```agda
module _
  {l1 l2 l3 l4 : Level} (X : Metric-Space l1 l2) (Y : Metric-Space l3 l4)
  (f : map-type-Metric-Space X Y)
  where

  is-modulus-of-uniform-continuity-prop-Metric-Space :
    (ℚ⁺ → ℚ⁺) → Prop (l1 ⊔ l2 ⊔ l4)
  modulus-of-uniform-continuity-Metric-Space-Prop m =
    Π-Prop
      ( type-Metric-Space X)
      ( λ x → modulus-of-continuity-at-point-Metric-Space-Prop X Y f x m)

  uniformly-continuous-Metric-Space-Prop : Prop (l1 ⊔ l2 ⊔ l4)
  uniformly-continuous-Metric-Space-Prop =
    is-inhabited-subtype-Prop modulus-of-uniform-continuity-Metric-Space-Prop

  is-uniformly-continuous-map-Metric-Space : UU (l1 ⊔ l2 ⊔ l4)
  is-uniformly-continuous-map-Metric-Space =
    type-Prop uniformly-continuous-Metric-Space-Prop

  is-continuous-at-point-is-uniformly-continuous-map-Metric-Space :
    is-uniformly-continuous-map-Metric-Space → (x : type-Metric-Space X) →
    is-continuous-at-point-Metric-Space X Y f x
  is-continuous-at-point-is-uniformly-continuous-map-Metric-Space H x =
    do
      m , is-modulus-uniform-m ← H
      intro-exists m (is-modulus-uniform-m x)
    where
      open do-syntax-trunc-Prop (continuous-at-point-Metric-Space-Prop X Y f x)
```

## Properties

### The identity function is uniformly continuous

```agda
module _
  {l1 l2 : Level} (X : Metric-Space l1 l2)
  where

  is-uniformly-continuous-map-id-Metric-Space :
    is-uniformly-continuous-map-Metric-Space X X id
  uniformly-continuous-id-Metric-Space = intro-exists id (λ _ _ _ → id)
```

### The composition of uniformly continuous functions is uniformly continuous

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (X : Metric-Space l1 l2) (Y : Metric-Space l3 l4) (Z : Metric-Space l5 l6)
  (f : map-type-Metric-Space Y Z) (g : map-type-Metric-Space X Y)
  where

  is-uniformly-continuous-map-comp-Metric-Space :
    is-uniformly-continuous-map-Metric-Space Y Z f →
    is-uniformly-continuous-map-Metric-Space X Y g →
    is-uniformly-continuous-map-Metric-Space X Z (f ∘ g)
  uniformly-continuous-comp-uniformly-continuous-Metric-Space H K =
    do
      mf , is-modulus-uniform-mf ← H
      mg , is-modulus-uniform-mg ← K
      intro-exists
        ( mg ∘ mf)
        ( λ x ε x' →
          is-modulus-uniform-mf (g x) ε (g x') ∘
          is-modulus-uniform-mg x (mf ε) x')
    where
      open
        do-syntax-trunc-Prop
          ( uniformly-continuous-Metric-Space-Prop X Z (f ∘ g))
```
