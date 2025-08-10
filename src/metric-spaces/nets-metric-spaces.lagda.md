# Nets in metric spaces

```agda
module metric-spaces.nets-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.natural-numbers

open import foundation.universe-levels
open import foundation.subtypes
open import foundation.dependent-pair-types
open import univalent-combinatorics.finite-subtypes
open import metric-spaces.metric-spaces
open import foundation.propositional-truncations
open import univalent-combinatorics.finitely-enumerable-subtypes
open import foundation.propositions
open import metric-spaces.approximations-metric-spaces
open import metric-spaces.located-metric-spaces
open import univalent-combinatorics.finitely-enumerable-types
```

</details>

## Idea

For an `ε : ℚ⁺`, an
`ε`-{{#concept "net" disambiguation="in a metric space"}} to a
[metric space](metric-spaces.metric-spaces.md) `X` is a
[finite](univalent-combinatorics.finite-subtypes.md)
ε-[approximation](metric-spaces.approximations-metric-spaces.md) of `X`.

This terminology is taken from {{#cite UF13}} definition 11.5.3.

## Definition

```agda
module _
  {l1 l2 l3 : Level} (X : Metric-Space l1 l2) (ε : ℚ⁺)
  (S : finite-subtype l3 (type-Metric-Space X))
  where

  is-net-prop-Metric-Space : Prop (l1 ⊔ l2 ⊔ l3)
  is-net-prop-Metric-Space =
    is-approximation-prop-Metric-Space X ε (subtype-finite-subtype S)

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

## Properties

### For any `δ < ε`, if there is a finitely enumerable `δ`-approximation in a located metric space, there is an `ε`-net

Lemma 2.2.2 in {{#cite BV06}}.

```agda
net-finite-enumeration-approximation-Located-Metric-Space :
  {l1 l2 l3 : Level} (X : Located-Metric-Space l1 l2)
  (δ : ℚ⁺) (S : approximation-Located-Metric-Space l3 X δ)
  (ε : ℚ⁺) (δ<ε : le-ℚ⁺ δ ε) →
  finite-enumeration
    ( type-approximation-Located-Metric-Space X δ S) →
  type-trunc-Prop (net-Located-Metric-Space l3 X ε)
net-finite-enumeration-approximation-Located-Metric-Space
  X δ S ε δ<ε eS@(zero-ℕ , _) = {!   !}
```

## References

{{#bibliography}}
