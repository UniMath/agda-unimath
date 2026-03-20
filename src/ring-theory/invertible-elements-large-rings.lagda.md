# Invertible elements in large rings

```agda
{-# OPTIONS --lossy-unification #-}

module ring-theory.invertible-elements-large-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.logical-equivalences
open import foundation.transport-along-identifications
open import foundation.propositions
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import group-theory.invertible-elements-large-monoids

open import ring-theory.invertible-elements-rings
open import ring-theory.large-rings
```

</details>

## Idea

{{#concept "Invertible elements" Disambiguation="of a large ring" Agda=is-invertible-element-Large-Ring}}
of a [large ring](ring-theory.rings.md) are elements that have a two-sided
multiplicative inverse.

## Definition

```agda
module _
  {α : Level → Level}
  {β : Level → Level → Level}
  (R : Large-Ring α β)
  {l1 : Level}
  (x : type-Large-Ring R l1)
  where

  is-left-inverse-element-prop-Large-Ring :
    {l2 : Level} (y : type-Large-Ring R l2) → Prop (β (l1 ⊔ l2) lzero)
  is-left-inverse-element-prop-Large-Ring =
    is-left-inverse-element-prop-Large-Monoid
      ( large-monoid-mul-Large-Ring R)
      ( x)

  is-right-inverse-element-prop-Large-Ring :
    {l2 : Level} (y : type-Large-Ring R l2) → Prop (β (l1 ⊔ l2) lzero)
  is-right-inverse-element-prop-Large-Ring =
    is-right-inverse-element-prop-Large-Monoid
      ( large-monoid-mul-Large-Ring R)
      ( x)

  is-inverse-element-prop-Large-Ring :
    {l2 : Level} (y : type-Large-Ring R l2) → Prop (β (l1 ⊔ l2) lzero)
  is-inverse-element-prop-Large-Ring =
    is-inverse-element-prop-Large-Monoid
      ( large-monoid-mul-Large-Ring R)
      ( x)

  is-left-inverse-element-Large-Ring :
    {l2 : Level} (y : type-Large-Ring R l2) → UU (β (l1 ⊔ l2) lzero)
  is-left-inverse-element-Large-Ring =
    is-left-inverse-element-Large-Monoid
      ( large-monoid-mul-Large-Ring R)
      ( x)

  is-right-inverse-element-Large-Ring :
    {l2 : Level} (y : type-Large-Ring R l2) → UU (β (l1 ⊔ l2) lzero)
  is-right-inverse-element-Large-Ring =
    is-right-inverse-element-Large-Monoid
      ( large-monoid-mul-Large-Ring R)
      ( x)

  is-inverse-element-Large-Ring :
    {l2 : Level} (y : type-Large-Ring R l2) → UU (β (l1 ⊔ l2) lzero)
  is-inverse-element-Large-Ring =
    is-inverse-element-Large-Monoid
      ( large-monoid-mul-Large-Ring R)
      ( x)

  is-left-invertible-element-Large-Ring : UU (α l1 ⊔ β l1 lzero)
  is-left-invertible-element-Large-Ring =
    is-left-invertible-element-Large-Monoid
      ( large-monoid-mul-Large-Ring R)
      ( x)

  is-right-invertible-element-Large-Ring : UU (α l1 ⊔ β l1 lzero)
  is-right-invertible-element-Large-Ring =
    is-right-invertible-element-Large-Monoid
      ( large-monoid-mul-Large-Ring R)
      ( x)

  is-invertible-element-Large-Ring : UU (α l1 ⊔ β l1 lzero)
  is-invertible-element-Large-Ring =
    is-invertible-element-Large-Monoid
      ( large-monoid-mul-Large-Ring R)
      ( x)

  inv-is-invertible-element-Large-Ring :
    is-invertible-element-Large-Ring → type-Large-Ring R l1
  inv-is-invertible-element-Large-Ring =
    inv-is-invertible-element-Large-Monoid
      ( large-monoid-mul-Large-Ring R)
      ( x)

  is-inverse-inv-is-invertible-element-Large-Ring :
    (H : is-invertible-element-Large-Ring) →
    is-inverse-element-Large-Ring (inv-is-invertible-element-Large-Ring H)
  is-inverse-inv-is-invertible-element-Large-Ring =
    is-inverse-inv-is-invertible-element-Large-Monoid
      ( large-monoid-mul-Large-Ring R)
      ( x)
```

## Properties

### Being an invertible element is a proposition

```agda
module _
  {α : Level → Level}
  {β : Level → Level → Level}
  (R : Large-Ring α β)
  {l1 : Level}
  (x : type-Large-Ring R l1)
  where

  abstract
    is-prop-is-invertible-element-Large-Ring :
      is-prop (is-invertible-element-Large-Ring R x)
    is-prop-is-invertible-element-Large-Ring =
      is-prop-is-invertible-element-Large-Monoid
        ( large-monoid-mul-Large-Ring R)
        ( x)

  is-invertible-element-prop-Large-Ring : Prop (α l1 ⊔ β l1 lzero)
  is-invertible-element-prop-Large-Ring =
    is-invertible-element-prop-Large-Monoid
      ( large-monoid-mul-Large-Ring R)
      ( x)
```

### If `x` is invertible, so is its inverse

```agda
module _
  {α : Level → Level}
  {β : Level → Level → Level}
  (R : Large-Ring α β)
  {l1 : Level}
  (x : type-Large-Ring R l1)
  where

  inverse-is-invertible-element-Large-Ring :
    (H : is-invertible-element-Large-Ring R x) →
    is-invertible-element-Large-Ring R
      ( inv-is-invertible-element-Large-Ring R x H)
  inverse-is-invertible-element-Large-Ring =
    inverse-is-invertible-element-Large-Monoid
      ( large-monoid-mul-Large-Ring R)
      ( x)
```

### An element is invertible in a large ring if and only if it is invertible in the corresponding small ring

```agda
module _
  {α : Level → Level}
  {β : Level → Level → Level}
  (R : Large-Ring α β)
  {l1 : Level}
  (x : type-Large-Ring R l1)
  where

  is-invertible-small-is-invertible-element-Large-Ring :
    is-invertible-element-Large-Ring R x →
    is-invertible-element-Ring (ring-Large-Ring R l1) x
  is-invertible-small-is-invertible-element-Large-Ring =
    is-invertible-small-is-invertible-element-Large-Monoid
      ( large-monoid-mul-Large-Ring R)
      ( x)

  is-invertible-is-invertible-small-element-Large-Ring :
    is-invertible-element-Ring (ring-Large-Ring R l1) x →
    is-invertible-element-Large-Ring R x
  is-invertible-is-invertible-small-element-Large-Ring =
    is-invertible-is-invertible-small-element-Large-Monoid
      ( large-monoid-mul-Large-Ring R)
      ( x)

  is-invertible-small-iff-is-invertible-element-Large-Ring :
    is-invertible-element-Large-Ring R x ↔
    is-invertible-element-Ring (ring-Large-Ring R l1) x
  is-invertible-small-iff-is-invertible-element-Large-Ring =
    is-invertible-small-iff-is-invertible-element-Large-Monoid
      ( large-monoid-mul-Large-Ring R)
      ( x)
```

### Invertible elements are closed under multiplication

```agda
module _
  {α : Level → Level}
  {β : Level → Level → Level}
  (R : Large-Ring α β)
  {l1 l2 : Level}
  (x : type-Large-Ring R l1)
  (y : type-Large-Ring R l2)
  where

  is-left-invertible-element-mul-Large-Ring :
    is-left-invertible-element-Large-Ring R x →
    is-left-invertible-element-Large-Ring R y →
    is-left-invertible-element-Large-Ring R (mul-Large-Ring R x y)
  is-left-invertible-element-mul-Large-Ring =
    is-left-invertible-element-mul-Large-Monoid
      ( large-monoid-mul-Large-Ring R)
      ( x)
      ( y)

  is-right-invertible-element-mul-Large-Ring :
    is-right-invertible-element-Large-Ring R x →
    is-right-invertible-element-Large-Ring R y →
    is-right-invertible-element-Large-Ring R (mul-Large-Ring R x y)
  is-right-invertible-element-mul-Large-Ring =
    is-right-invertible-element-mul-Large-Monoid
      ( large-monoid-mul-Large-Ring R)
      ( x)
      ( y)

  is-invertible-element-mul-Large-Ring :
    is-invertible-element-Large-Ring R x →
    is-invertible-element-Large-Ring R y →
    is-invertible-element-Large-Ring R (mul-Large-Ring R x y)
  is-invertible-element-mul-Large-Ring =
    is-invertible-element-mul-Large-Monoid
      ( large-monoid-mul-Large-Ring R)
      ( x)
      ( y)
```

### Invertible elements are closed under negation

```agda
module _
  {α : Level → Level}
  {β : Level → Level → Level}
  (R : Large-Ring α β)
  {l1 : Level}
  (x : type-Large-Ring R l1)
  where

  is-left-invertible-element-neg-Large-Ring :
    is-left-invertible-element-Large-Ring R x →
    is-left-invertible-element-Large-Ring R (neg-Large-Ring R x)
  is-left-invertible-element-neg-Large-Ring (y , yx~1) =
    ( neg-Large-Ring R y ,
      inv-tr
        ( is-one-Large-Ring R)
        ( negative-law-mul-Large-Ring R y x)
        ( yx~1))

  is-right-invertible-element-neg-Large-Ring :
    is-right-invertible-element-Large-Ring R x →
    is-right-invertible-element-Large-Ring R (neg-Large-Ring R x)
  is-right-invertible-element-neg-Large-Ring (y , xy~1) =
    ( neg-Large-Ring R y ,
      inv-tr
        ( is-one-Large-Ring R)
        ( negative-law-mul-Large-Ring R x y)
        ( xy~1))

  is-invertible-element-neg-Large-Ring :
    is-invertible-element-Large-Ring R x →
    is-invertible-element-Large-Ring R (neg-Large-Ring R x)
  is-invertible-element-neg-Large-Ring (y , xy~1 , yx~1) =
    ( neg-Large-Ring R y ,
      pr2 (is-right-invertible-element-neg-Large-Ring (y , xy~1)) ,
      pr2 (is-left-invertible-element-neg-Large-Ring (y , yx~1)))
```

### Invertible elements are closed under raising universe level

```agda
module _
  {α : Level → Level}
  {β : Level → Level → Level}
  (R : Large-Ring α β)
  {l1 : Level}
  (l2 : Level)
  (x : type-Large-Ring R l1)
  where

  is-invertible-element-raise-Large-Ring :
    is-invertible-element-Large-Ring R x →
    is-invertible-element-Large-Ring R (raise-Large-Ring R l2 x)
  is-invertible-element-raise-Large-Ring =
    is-invertible-element-raise-Large-Monoid
      ( large-monoid-mul-Large-Ring R)
      ( l2)
      ( x)
```

## See also

- [Invertible elements in (small) rings](ring-theory.invertible-elements-rings.md)
