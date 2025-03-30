# Continuous functions between metric spaces

```agda
module metric-spaces.continuous-functions-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.inhabited-subtypes
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import metric-spaces.functions-metric-spaces
open import metric-spaces.metric-spaces
```

</details>

## Idea

A [function](metric-spaces.functions-metric-spaces.md) `f` between
[metric spaces](metric-spaces.metric-spaces.md) `X` and `Y` is
{{#concept "continuous" Disambiguation="function between metric spaces at a point" WDID=Q170058 WD="continuous function" Agda=is-continuous-at-point-Metric-Space}}
at a point `x` if there exists a function `m : ℚ⁺ → ℚ⁺` such that whenever `x'`
is in an `m ε`-neighborhood of `x`, `f x'` is in an `ε`-neighborhood of `f x`.
`m` is called a modulus of continuity of `f` at `x`.

## Definitions

```agda
module _
  {l1 l2 l3 l4 : Level} (X : Metric-Space l1 l2) (Y : Metric-Space l3 l4)
  (f : map-type-Metric-Space X Y)
  where

  is-modulus-of-continuity-at-point-prop-Metric-Space :
    (x : type-Metric-Space X) → (ℚ⁺ → ℚ⁺) → Prop (l1 ⊔ l2 ⊔ l4)
  modulus-of-continuity-at-point-Metric-Space-Prop x m =
    Π-Prop
      ( ℚ⁺)
      ( λ ε →
        Π-Prop
          ( type-Metric-Space X)
          ( λ x' →
            structure-Metric-Space X (m ε) x x' ⇒
            structure-Metric-Space Y ε (f x) (f x')))

  is-modulus-of-continuity-at-point-Metric-Space :
    (x : type-Metric-Space X) → UU (l1 ⊔ l2 ⊔ l4)
  modulus-of-continuity-at-point-Metric-Space x =
    type-subtype (modulus-of-continuity-at-point-Metric-Space-Prop x)

  is-continuous-at-point-prop-Metric-Space :
    (x : type-Metric-Space X) → Prop (l1 ⊔ l2 ⊔ l4)
  continuous-at-point-Metric-Space-Prop x =
    is-inhabited-subtype-Prop
      (modulus-of-continuity-at-point-Metric-Space-Prop x)

  is-continuous-at-point-Metric-Space :
    (x : type-Metric-Space X) → UU (l1 ⊔ l2 ⊔ l4)
  is-continuous-at-point-Metric-Space x =
    type-Prop (continuous-at-point-Metric-Space-Prop x)
```
