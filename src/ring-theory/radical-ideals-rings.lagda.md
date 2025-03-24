# Radical ideals of rings

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module ring-theory.radical-ideals-rings
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-products-propositions funext
open import foundation.propositions funext univalence
open import foundation.universe-levels

open import ring-theory.ideals-rings funext univalence truncations
open import ring-theory.invertible-elements-rings funext univalence truncations
open import ring-theory.rings funext univalence truncations
```

</details>

## Idea

A radical ideal in a ring R is an ideal I such that `1 + x` is a multiplicative
unit for every `x ∈ I`.

## Definition

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (I : ideal-Ring l2 R)
  where

  is-radical-ideal-prop-Ring : Prop (l1 ⊔ l2)
  is-radical-ideal-prop-Ring =
    Π-Prop
      ( type-ideal-Ring R I)
      ( λ x →
        is-invertible-element-prop-Ring R
          ( add-Ring R (one-Ring R) (inclusion-ideal-Ring R I x)))

  is-radical-ideal-Ring : UU (l1 ⊔ l2)
  is-radical-ideal-Ring =
    type-Prop is-radical-ideal-prop-Ring

  is-prop-is-radical-ideal-Ring :
    is-prop is-radical-ideal-Ring
  is-prop-is-radical-ideal-Ring =
    is-prop-type-Prop is-radical-ideal-prop-Ring
```
