# The center of a ring

```agda
module commutative-algebra.centers-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.centers-monoids

open import ring-theory.central-elements-rings
open import ring-theory.rings
open import ring-theory.subrings
open import ring-theory.subsets-rings
```

</details>

## Idea

The
{{#concept "center" WDID=Q30603786 WD="center" Disambiguation="of a ring" Agda=subring-center-Ring}}
of a [ring](ring-theory.rings.md) `R` is the [subring](ring-theory.subrings.md)
of `R` consisting of [central](ring-theory.central-elements-rings.md) elements
of `R`. The center is always a
[commutative ring](commutative-algebra.commutative-rings.md).

## Definition

```agda
module _
  {l : Level}
  (R : Ring l)
  where

  subtype-center-Ring : subset-Ring l R
  subtype-center-Ring = is-central-element-prop-Ring R

  subring-center-Ring : Subring l R
  subring-center-Ring =
    ( subtype-center-Ring ,
      is-central-element-zero-Ring R ,
      is-central-element-one-Ring R ,
      is-central-element-add-Ring R _ _ ,
      is-central-element-neg-Ring R _ ,
      is-central-element-mul-Ring R)

  ring-center-Ring : Ring l
  ring-center-Ring = ring-Subring R subring-center-Ring

  type-center-Ring : UU l
  type-center-Ring = type-Ring ring-center-Ring

  mul-center-Ring : type-center-Ring → type-center-Ring → type-center-Ring
  mul-center-Ring = mul-Ring ring-center-Ring

  abstract
    commutative-mul-center-Ring :
      (x y : type-center-Ring) →
      mul-center-Ring x y ＝ mul-center-Ring y x
    commutative-mul-center-Ring =
      commutative-mul-center-Monoid (multiplicative-monoid-Ring R)

  commutative-ring-center-Ring : Commutative-Ring l
  commutative-ring-center-Ring =
    ( ring-center-Ring ,
      commutative-mul-center-Ring)
```

## External links

- [Center (ring theory)](<https://en.wikipedia.org/wiki/Center_(ring_theory)>)
  on Wikipedia
