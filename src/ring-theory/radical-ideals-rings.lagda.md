# Radical ideals of rings

```agda
module ring-theory.radical-ideals-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-products-propositions
open import foundation.propositions
open import foundation.universe-levels

open import ring-theory.ideals-rings
open import ring-theory.invertible-elements-rings
open import ring-theory.rings
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
