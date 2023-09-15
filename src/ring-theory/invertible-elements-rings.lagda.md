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
a two-sided multiplicative inverse. Such elements are also called the
**(multiplicative) units** of the ring. The [set](foundation.sets.md) of units
of any ring forms a [group](group-theory.groups.md).

## Definitions

### Left invertible elements of rings

```agda
module _
  {l : Level} (R : Ring l)
  where

  is-left-inverse-element-Ring : (x y : type-Ring R) → UU l
  is-left-inverse-element-Ring =
    is-left-inverse-element-Monoid (multiplicative-monoid-Ring R)

  is-left-invertible-element-Ring : type-Ring R → UU l
  is-left-invertible-element-Ring =
    is-left-invertible-element-Monoid (multiplicative-monoid-Ring R)

module _
  {l : Level} (R : Ring l) {x : type-Ring R}
  where

  retraction-is-left-invertible-element-Ring :
    is-left-invertible-element-Ring R x → type-Ring R
  retraction-is-left-invertible-element-Ring =
    retraction-is-left-invertible-element-Monoid
      ( multiplicative-monoid-Ring R)

  is-left-inverse-retraction-is-left-invertible-element-Ring :
    (H : is-left-invertible-element-Ring R x) →
    is-left-inverse-element-Ring R x
      ( retraction-is-left-invertible-element-Ring H)
  is-left-inverse-retraction-is-left-invertible-element-Ring =
    is-left-inverse-retraction-is-left-invertible-element-Monoid
      ( multiplicative-monoid-Ring R)
```

### Right invertible elements of rings

```agda
module _
  {l : Level} (R : Ring l)
  where

  is-right-inverse-element-Ring : (x y : type-Ring R) → UU l
  is-right-inverse-element-Ring =
    is-right-inverse-element-Monoid (multiplicative-monoid-Ring R)

  is-right-invertible-element-Ring : type-Ring R → UU l
  is-right-invertible-element-Ring =
    is-right-invertible-element-Monoid (multiplicative-monoid-Ring R)

module _
  {l : Level} (R : Ring l) {x : type-Ring R}
  where

  section-is-right-invertible-element-Ring :
    is-right-invertible-element-Ring R x → type-Ring R
  section-is-right-invertible-element-Ring =
    section-is-right-invertible-element-Monoid (multiplicative-monoid-Ring R)

  is-right-inverse-section-is-right-invertible-element-Ring :
    (H : is-right-invertible-element-Ring R x) →
    is-right-inverse-element-Ring R x
      ( section-is-right-invertible-element-Ring H)
  is-right-inverse-section-is-right-invertible-element-Ring =
    is-right-inverse-section-is-right-invertible-element-Monoid
      ( multiplicative-monoid-Ring R)
```

### Invertible elements of rings

```agda
module _
  {l : Level} (R : Ring l)
  where

  has-two-sided-inverse-Ring : type-Ring R → UU l
  has-two-sided-inverse-Ring x =
    ( is-left-invertible-element-Ring R x) ×
    ( is-right-invertible-element-Ring R x)

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
