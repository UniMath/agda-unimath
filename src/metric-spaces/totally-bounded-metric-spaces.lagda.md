# Totally bounded metric spaces

```agda
module metric-spaces.totally-bounded-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.universe-levels

open import metric-spaces.metric-spaces
open import metric-spaces.nets-metric-spaces
```

</details>

## Idea

A [metric space](metric-spaces.metric-spaces.md) is
{{#concept "totally bounded" WDID=Q1362228 WD="totally bounded space" Agda=is-totally-bounded-Metric-Space}}
if for every `ε : ℚ⁺`, it has an `ε`-[net](metric-spaces.nets-metric-spaces.md).

## Definition

```agda
module _
  {l1 l2 : Level} (X : Metric-Space l1 l2)
  where

  modulus-of-total-boundedness-Metric-Space : UU (lsuc l1 ⊔ lsuc l2)
  modulus-of-total-boundedness-Metric-Space =
    (ε : ℚ⁺) → net-Metric-Space (l1 ⊔ l2) X ε

  is-totally-bounded-prop-Metric-Space : Prop (lsuc l1 ⊔ lsuc l2)
  is-totally-bounded-prop-Metric-Space =
    trunc-Prop modulus-of-total-boundedness-Metric-Space

  is-totally-bounded-Metric-Space : UU (lsuc l1 ⊔ lsuc l2)
  is-totally-bounded-Metric-Space =
    type-Prop is-totally-bounded-prop-Metric-Space
```
