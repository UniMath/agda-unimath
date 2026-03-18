# Invertible elements in large rings

```agda
{-# OPTIONS --lossy-unification #-}

module commutative-algebra.invertible-elements-large-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.invertible-elements-commutative-rings
open import commutative-algebra.large-commutative-rings

open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.universe-levels

open import ring-theory.invertible-elements-large-rings
```

</details>

## Idea

{{#concept "Invertible elements" Disambiguation="of a large commutative ring" Agda=is-invertible-element-Large-Commutative-Ring}}
of a [large commutative ring](commutative-algebra.commutative-rings.md) are
elements that have a two-sided multiplicative inverse.

## Definition

```agda
module _
  {α : Level → Level}
  {β : Level → Level → Level}
  (R : Large-Commutative-Ring α β)
  {l1 : Level}
  (x : type-Large-Commutative-Ring R l1)
  where

  is-left-inverse-element-prop-Large-Commutative-Ring :
    {l2 : Level} (y : type-Large-Commutative-Ring R l2) →
    Prop (β (l1 ⊔ l2) lzero)
  is-left-inverse-element-prop-Large-Commutative-Ring =
    is-left-inverse-element-prop-Large-Ring
      ( large-ring-Large-Commutative-Ring R)
      ( x)

  is-right-inverse-element-prop-Large-Commutative-Ring :
    {l2 : Level} (y : type-Large-Commutative-Ring R l2) →
    Prop (β (l1 ⊔ l2) lzero)
  is-right-inverse-element-prop-Large-Commutative-Ring =
    is-right-inverse-element-prop-Large-Ring
      ( large-ring-Large-Commutative-Ring R)
      ( x)

  is-inverse-element-prop-Large-Commutative-Ring :
    {l2 : Level} (y : type-Large-Commutative-Ring R l2) →
    Prop (β (l1 ⊔ l2) lzero)
  is-inverse-element-prop-Large-Commutative-Ring =
    is-inverse-element-prop-Large-Ring
      ( large-ring-Large-Commutative-Ring R)
      ( x)

  is-left-inverse-element-Large-Commutative-Ring :
    {l2 : Level} (y : type-Large-Commutative-Ring R l2) → UU (β (l1 ⊔ l2) lzero)
  is-left-inverse-element-Large-Commutative-Ring =
    is-left-inverse-element-Large-Ring
      ( large-ring-Large-Commutative-Ring R)
      ( x)

  is-right-inverse-element-Large-Commutative-Ring :
    {l2 : Level} (y : type-Large-Commutative-Ring R l2) → UU (β (l1 ⊔ l2) lzero)
  is-right-inverse-element-Large-Commutative-Ring =
    is-right-inverse-element-Large-Ring
      ( large-ring-Large-Commutative-Ring R)
      ( x)

  is-inverse-element-Large-Commutative-Ring :
    {l2 : Level} (y : type-Large-Commutative-Ring R l2) → UU (β (l1 ⊔ l2) lzero)
  is-inverse-element-Large-Commutative-Ring =
    is-inverse-element-Large-Ring
      ( large-ring-Large-Commutative-Ring R)
      ( x)

  is-left-invertible-element-Large-Commutative-Ring : UU (α l1 ⊔ β l1 lzero)
  is-left-invertible-element-Large-Commutative-Ring =
    is-left-invertible-element-Large-Ring
      ( large-ring-Large-Commutative-Ring R)
      ( x)

  is-right-invertible-element-Large-Commutative-Ring : UU (α l1 ⊔ β l1 lzero)
  is-right-invertible-element-Large-Commutative-Ring =
    is-right-invertible-element-Large-Ring
      ( large-ring-Large-Commutative-Ring R)
      ( x)

  is-invertible-element-Large-Commutative-Ring : UU (α l1 ⊔ β l1 lzero)
  is-invertible-element-Large-Commutative-Ring =
    is-invertible-element-Large-Ring
      ( large-ring-Large-Commutative-Ring R)
      ( x)

  inv-is-invertible-element-Large-Commutative-Ring :
    is-invertible-element-Large-Commutative-Ring →
    type-Large-Commutative-Ring R l1
  inv-is-invertible-element-Large-Commutative-Ring =
    inv-is-invertible-element-Large-Ring
      ( large-ring-Large-Commutative-Ring R)
      ( x)

  is-inverse-inv-is-invertible-element-Large-Commutative-Ring :
    (H : is-invertible-element-Large-Commutative-Ring) →
    is-inverse-element-Large-Commutative-Ring
      ( inv-is-invertible-element-Large-Commutative-Ring H)
  is-inverse-inv-is-invertible-element-Large-Commutative-Ring =
    is-inverse-inv-is-invertible-element-Large-Ring
      ( large-ring-Large-Commutative-Ring R)
      ( x)
```

## Properties

### Being an invertible element is a proposition

```agda
module _
  {α : Level → Level}
  {β : Level → Level → Level}
  (R : Large-Commutative-Ring α β)
  {l1 : Level}
  (x : type-Large-Commutative-Ring R l1)
  where

  abstract
    is-prop-is-invertible-element-Large-Commutative-Ring :
      is-prop (is-invertible-element-Large-Commutative-Ring R x)
    is-prop-is-invertible-element-Large-Commutative-Ring =
      is-prop-is-invertible-element-Large-Ring
        ( large-ring-Large-Commutative-Ring R)
        ( x)

  is-invertible-element-prop-Large-Commutative-Ring : Prop (α l1 ⊔ β l1 lzero)
  is-invertible-element-prop-Large-Commutative-Ring =
    is-invertible-element-prop-Large-Ring
      ( large-ring-Large-Commutative-Ring R)
      ( x)
```

### If `x` is invertible, so is its inverse

```agda
module _
  {α : Level → Level}
  {β : Level → Level → Level}
  (R : Large-Commutative-Ring α β)
  {l1 : Level}
  (x : type-Large-Commutative-Ring R l1)
  where

  inverse-is-invertible-element-Large-Commutative-Ring :
    (H : is-invertible-element-Large-Commutative-Ring R x) →
    is-invertible-element-Large-Commutative-Ring R
      ( inv-is-invertible-element-Large-Commutative-Ring R x H)
  inverse-is-invertible-element-Large-Commutative-Ring =
    inverse-is-invertible-element-Large-Ring
      ( large-ring-Large-Commutative-Ring R)
      ( x)
```

### An element is invertible in a large commutative ring if and only if it is invertible in the corresponding small commutative ring

```agda
module _
  {α : Level → Level}
  {β : Level → Level → Level}
  (R : Large-Commutative-Ring α β)
  {l1 : Level}
  (x : type-Large-Commutative-Ring R l1)
  where

  is-invertible-small-is-invertible-element-Large-Commutative-Ring :
    is-invertible-element-Large-Commutative-Ring R x →
    is-invertible-element-Commutative-Ring
      ( commutative-ring-Large-Commutative-Ring R l1)
      ( x)
  is-invertible-small-is-invertible-element-Large-Commutative-Ring =
    is-invertible-small-is-invertible-element-Large-Ring
      ( large-ring-Large-Commutative-Ring R)
      ( x)

  is-invertible-is-invertible-small-element-Large-Commutative-Ring :
    is-invertible-element-Commutative-Ring
      ( commutative-ring-Large-Commutative-Ring R l1)
      ( x) →
    is-invertible-element-Large-Commutative-Ring R x
  is-invertible-is-invertible-small-element-Large-Commutative-Ring =
    is-invertible-is-invertible-small-element-Large-Ring
      ( large-ring-Large-Commutative-Ring R)
      ( x)

  is-invertible-small-iff-is-invertible-element-Large-Commutative-Ring :
    is-invertible-element-Large-Commutative-Ring R x ↔
    is-invertible-element-Commutative-Ring
      ( commutative-ring-Large-Commutative-Ring R l1)
      ( x)
  is-invertible-small-iff-is-invertible-element-Large-Commutative-Ring =
    is-invertible-small-iff-is-invertible-element-Large-Ring
      ( large-ring-Large-Commutative-Ring R)
      ( x)
```

### Invertible elements are closed under multiplication

```agda
module _
  {α : Level → Level}
  {β : Level → Level → Level}
  (R : Large-Commutative-Ring α β)
  {l1 l2 : Level}
  (x : type-Large-Commutative-Ring R l1)
  (y : type-Large-Commutative-Ring R l2)
  where

  is-left-invertible-element-mul-Large-Commutative-Ring :
    is-left-invertible-element-Large-Commutative-Ring R x →
    is-left-invertible-element-Large-Commutative-Ring R y →
    is-left-invertible-element-Large-Commutative-Ring R
      ( mul-Large-Commutative-Ring R x y)
  is-left-invertible-element-mul-Large-Commutative-Ring =
    is-left-invertible-element-mul-Large-Ring
      ( large-ring-Large-Commutative-Ring R)
      ( x)
      ( y)

  is-right-invertible-element-mul-Large-Commutative-Ring :
    is-right-invertible-element-Large-Commutative-Ring R x →
    is-right-invertible-element-Large-Commutative-Ring R y →
    is-right-invertible-element-Large-Commutative-Ring R
      ( mul-Large-Commutative-Ring R x y)
  is-right-invertible-element-mul-Large-Commutative-Ring =
    is-right-invertible-element-mul-Large-Ring
      ( large-ring-Large-Commutative-Ring R)
      ( x)
      ( y)

  is-invertible-element-mul-Large-Commutative-Ring :
    is-invertible-element-Large-Commutative-Ring R x →
    is-invertible-element-Large-Commutative-Ring R y →
    is-invertible-element-Large-Commutative-Ring R
      ( mul-Large-Commutative-Ring R x y)
  is-invertible-element-mul-Large-Commutative-Ring =
    is-invertible-element-mul-Large-Ring
      ( large-ring-Large-Commutative-Ring R)
      ( x)
      ( y)
```

### Invertible elements are closed under negation

```agda
module _
  {α : Level → Level}
  {β : Level → Level → Level}
  (R : Large-Commutative-Ring α β)
  {l1 : Level}
  (x : type-Large-Commutative-Ring R l1)
  where

  is-left-invertible-element-neg-Large-Commutative-Ring :
    is-left-invertible-element-Large-Commutative-Ring R x →
    is-left-invertible-element-Large-Commutative-Ring R
      ( neg-Large-Commutative-Ring R x)
  is-left-invertible-element-neg-Large-Commutative-Ring =
    is-left-invertible-element-neg-Large-Ring
      ( large-ring-Large-Commutative-Ring R)
      ( x)

  is-right-invertible-element-neg-Large-Commutative-Ring :
    is-right-invertible-element-Large-Commutative-Ring R x →
    is-right-invertible-element-Large-Commutative-Ring R
      ( neg-Large-Commutative-Ring R x)
  is-right-invertible-element-neg-Large-Commutative-Ring =
    is-right-invertible-element-neg-Large-Ring
      ( large-ring-Large-Commutative-Ring R)
      ( x)

  is-invertible-element-neg-Large-Commutative-Ring :
    is-invertible-element-Large-Commutative-Ring R x →
    is-invertible-element-Large-Commutative-Ring R
      ( neg-Large-Commutative-Ring R x)
  is-invertible-element-neg-Large-Commutative-Ring =
    is-invertible-element-neg-Large-Ring
      ( large-ring-Large-Commutative-Ring R)
      ( x)
```

## See also

- [Invertible elements in (small) commutative rings](commutative-algebra.invertible-elements-commutative-rings.md)
