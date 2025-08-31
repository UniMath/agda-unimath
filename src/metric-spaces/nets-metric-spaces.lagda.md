# Nets in metric spaces

```agda
module metric-spaces.nets-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.inhabited-types
open import foundation.propositions
open import foundation.dependent-pair-types
open import foundation.subtypes
open import foundation.universe-levels

open import metric-spaces.approximations-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.images-metric-spaces
open import metric-spaces.functions-metric-spaces
open import metric-spaces.uniformly-continuous-functions-metric-spaces

open import univalent-combinatorics.finitely-enumerable-subtypes
open import univalent-combinatorics.finitely-enumerable-types
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

module _
  {l1 l2 l3 : Level} (X : Metric-Space l1 l2) (ε : ℚ⁺)
  (N : net-Metric-Space l3 X ε)
  where

  finitely-enumerable-subset-net-Metric-Space :
    finitely-enumerable-subtype l3 (type-Metric-Space X)
  finitely-enumerable-subset-net-Metric-Space = pr1 N

  subset-net-Metric-Space : subtype l3 (type-Metric-Space X)
  subset-net-Metric-Space =
    subtype-finitely-enumerable-subtype
      ( finitely-enumerable-subset-net-Metric-Space)

  is-approximation-net-Metric-Space :
    is-approximation-Metric-Space X ε subset-net-Metric-Space
  is-approximation-net-Metric-Space = pr2 N
```

### If a metric space is inhabited, so is any net

```agda
module _
  {l1 l2 l3 : Level}
  (X : Metric-Space l1 l2) (|X| : is-inhabited (type-Metric-Space X))
  (ε : ℚ⁺) (S : net-Metric-Space l3 X ε)
  where

  abstract
    is-inhabited-net-inhabited-Metric-Space :
      is-inhabited-finitely-enumerable-subtype (pr1 S)
    is-inhabited-net-inhabited-Metric-Space =
      is-inhabited-is-approximation-inhabited-Metric-Space X |X| ε
        ( subset-net-Metric-Space X ε S)
        ( is-approximation-net-Metric-Space X ε S)
```

## Properties

### If `μ` is a modulus of uniform continuity for `f : X → Y` and `A` is a `(μ ε)`-net of `X`, then `im f A` is an `ε`-net of `im f X`

```agda
module _
  {l1 l2 l3 l4 l5 : Level} (X : Metric-Space l1 l2) (Y : Metric-Space l3 l4)
  (f : type-function-Metric-Space X Y) {μ : ℚ⁺ → ℚ⁺}
  (is-modulus-ucont-f-μ :
    is-modulus-of-uniform-continuity-function-Metric-Space X Y f μ)
  (ε : ℚ⁺) (A : net-Metric-Space l5 X (μ ε))
  where

  net-im-uniformly-continuous-function-net-Metric-Space :
    net-Metric-Space (l1 ⊔ l3 ⊔ l5) (im-Metric-Space X Y f) ε
  net-im-uniformly-continuous-function-net-Metric-Space =
    ( ? ,
      ?)
```
