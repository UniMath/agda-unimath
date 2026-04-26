# Nets in located metric spaces

```agda
module metric-spaces.nets-located-metric-spaces where
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
open import metric-spaces.nets-metric-spaces

open import univalent-combinatorics.finite-subtypes
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.finitely-enumerable-subtypes
open import univalent-combinatorics.finitely-enumerable-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

For an `ε : ℚ⁺`, an
`ε`-{{#concept "net" disambiguation="in a located metric space" Agda=net-Located-Metric-Space}}
to a [located metric space](metric-spaces.located-metric-spaces.md) `X` is an
[`ε`-net](metric-spaces.nets-metric-spaces.md) in the underlying
[metric space](metric-spaces.metric-spaces.md).

## Definition

```agda
net-Located-Metric-Space :
  {l1 l2 : Level} (l3 : Level) → Located-Metric-Space l1 l2 → ℚ⁺ →
  UU (l1 ⊔ l2 ⊔ lsuc l3)
net-Located-Metric-Space l3 X =
  net-Metric-Space l3 (metric-space-Located-Metric-Space X)
```
