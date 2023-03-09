# Radical ideals in rings

```agda
module ring-theory.radical-ideals-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.propositions
open import foundation.universe-levels

open import ring-theory.ideals-rings
open import ring-theory.invertible-elements-rings
open import ring-theory.rings
```

</details>

## Idea

A radical ideal in a ring R is a two-sided ideal I such that `1 + x` is a multiplicative unit for every `x ∈ I`.

## Definition

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (I : two-sided-ideal-Ring l2 R)
  where

  is-radical-two-sided-ideal-ring-Prop : Prop (l1 ⊔ l2)
  is-radical-two-sided-ideal-ring-Prop =
    Π-Prop
      ( type-two-sided-ideal-Ring R I)
      ( λ x →
        is-invertible-element-ring-Prop R
          ( add-Ring R (one-Ring R) (inclusion-two-sided-ideal-Ring R I x)))

  is-radical-two-sided-ideal-Ring : UU (l1 ⊔ l2)
  is-radical-two-sided-ideal-Ring =
    type-Prop is-radical-two-sided-ideal-ring-Prop

  is-prop-is-radical-two-sided-ideal-Ring :
    is-prop is-radical-two-sided-ideal-Ring
  is-prop-is-radical-two-sided-ideal-Ring =
    is-prop-type-Prop is-radical-two-sided-ideal-ring-Prop
```
