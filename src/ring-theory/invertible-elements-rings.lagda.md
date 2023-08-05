# Invertible elements in rings

```agda
module ring-theory.invertible-elements-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels

open import group-theory.invertible-elements-monoids

open import ring-theory.rings
```

</details>

## Idea

**Invertible elements** in a [ring](ring-theory.rings.md) are elements that have
a two-sided multiplicative inverse. Such elements are also called the **units**
of the ring. The [set](foundation.sets.md) of units of any ring forms a
[group](group-theory.groups.md).

## Definition

```agda
module _
  {l : Level} (R : Ring l)
  where

  has-left-inverse-Ring : type-Ring R → UU l
  has-left-inverse-Ring x =
    Σ (type-Ring R) (λ y → Id (mul-Ring R y x) (one-Ring R))

  has-right-inverse-Ring : type-Ring R → UU l
  has-right-inverse-Ring x =
    Σ (type-Ring R) (λ y → Id (mul-Ring R x y) (one-Ring R))

  has-two-sided-inverse-Ring : type-Ring R → UU l
  has-two-sided-inverse-Ring x =
    ( has-left-inverse-Ring x) × (has-right-inverse-Ring x)

  is-invertible-element-ring-Prop : type-Ring R → Prop l
  is-invertible-element-ring-Prop =
    is-invertible-element-monoid-Prop (multiplicative-monoid-Ring R)

  is-invertible-element-Ring : type-Ring R → UU l
  is-invertible-element-Ring x =
    type-Prop (is-invertible-element-ring-Prop x)

  is-prop-is-invertible-element-Ring :
    (x : type-Ring R) → is-prop (is-invertible-element-Ring x)
  is-prop-is-invertible-element-Ring x =
    is-prop-type-Prop (is-invertible-element-ring-Prop x)
```
