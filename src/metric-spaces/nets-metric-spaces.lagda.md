# Nets in metric spaces

```agda
module metric-spaces.nets-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.existential-quantification
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.singleton-subtypes
open import foundation.subtypes
open import foundation.surjective-maps
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import metric-spaces.approximations-metric-spaces
open import metric-spaces.located-metric-spaces
open import metric-spaces.metric-spaces

open import univalent-combinatorics.finite-subtypes
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.finitely-enumerable-subtypes
open import univalent-combinatorics.finitely-enumerable-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

For an `ε : ℚ⁺`, an `ε`-{{#concept "net" disambiguation="in a metric space"}} to
a [metric space](metric-spaces.metric-spaces.md) `X` is a
[finitely enumerable](univalent-combinatorics.finitely-enumerable-subtypes.md)
ε-[approximation](metric-spaces.approximations-metric-spaces.md) of `X`.

## Definition

```agda
module _
  {l1 l2 l3 : Level} (X : Metric-Space l1 l2) (ε : ℚ⁺)
  (S : finitely-enumerable-subtype l3 (type-Metric-Space X))
  where

  is-net-prop-Metric-Space : Prop (l1 ⊔ l2 ⊔ l3)
  is-net-prop-Metric-Space =
    is-approximation-prop-Metric-Space X ε
      ( subtype-finitely-enumerable-subtype S)

  is-net-Metric-Space : UU (l1 ⊔ l2 ⊔ l3)
  is-net-Metric-Space = type-Prop is-net-prop-Metric-Space

net-Metric-Space :
  {l1 l2 : Level} (l3 : Level) → Metric-Space l1 l2 → ℚ⁺ →
  UU (l1 ⊔ l2 ⊔ lsuc l3)
net-Metric-Space l3 X ε =
  type-subtype (is-net-prop-Metric-Space {l3 = l3} X ε)
```

### In located metric spaces

```agda
net-Located-Metric-Space :
  {l1 l2 : Level} (l3 : Level) → Located-Metric-Space l1 l2 → ℚ⁺ →
  UU (l1 ⊔ l2 ⊔ lsuc l3)
net-Located-Metric-Space l3 X =
  net-Metric-Space l3 (metric-space-Located-Metric-Space X)
```
