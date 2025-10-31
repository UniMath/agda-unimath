# Central elements of rings

```agda
module ring-theory.central-elements-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels

open import ring-theory.central-elements-semirings
open import ring-theory.rings
```

</details>

## Idea

An element `x` of a [ring](ring-theory.rings.md) `R` is said to be
{{#concept "central" Disambiguation="element of a ring" Agda=is-central-element-Ring}}
if `xy ＝ yx` for every `y : R`.

## Definition

```agda
module _
  {l : Level} (R : Ring l)
  where

  is-central-element-ring-Prop : type-Ring R → Prop l
  is-central-element-ring-Prop =
    is-central-element-semiring-Prop (semiring-Ring R)

  is-central-element-Ring : type-Ring R → UU l
  is-central-element-Ring = is-central-element-Semiring (semiring-Ring R)

  is-prop-is-central-element-Ring :
    (x : type-Ring R) → is-prop (is-central-element-Ring x)
  is-prop-is-central-element-Ring =
    is-prop-is-central-element-Semiring (semiring-Ring R)
```

## Properties

### The zero element is central

```agda
module _
  {l : Level} (R : Ring l)
  where

  is-central-element-zero-Ring : is-central-element-Ring R (zero-Ring R)
  is-central-element-zero-Ring =
    is-central-element-zero-Semiring (semiring-Ring R)
```

### The unit element is central

```agda
module _
  {l : Level} (R : Ring l)
  where

  is-central-element-one-Ring : is-central-element-Ring R (one-Ring R)
  is-central-element-one-Ring =
    is-central-element-one-Semiring (semiring-Ring R)
```

### The sum of two central elements is central

```agda
module _
  {l : Level} (R : Ring l)
  where

  is-central-element-add-Ring :
    (x y : type-Ring R) → is-central-element-Ring R x →
    is-central-element-Ring R y → is-central-element-Ring R (add-Ring R x y)
  is-central-element-add-Ring =
    is-central-element-add-Semiring (semiring-Ring R)
```

### The negative of a central element is central

```agda
module _
  {l : Level} (R : Ring l)
  where

  is-central-element-neg-Ring :
    (x : type-Ring R) → is-central-element-Ring R x →
    is-central-element-Ring R (neg-Ring R x)
  is-central-element-neg-Ring x H y =
    ( left-negative-law-mul-Ring R x y) ∙
    ( ( ap (neg-Ring R) (H y)) ∙
      ( inv (right-negative-law-mul-Ring R y x)))
```

### `-1` is a central element

```agda
module _
  {l : Level} (R : Ring l)
  where

  is-central-element-neg-one-Ring :
    is-central-element-Ring R (neg-one-Ring R)
  is-central-element-neg-one-Ring =
    is-central-element-neg-Ring R (one-Ring R) (is-central-element-one-Ring R)
```

### The product of two central elements is central

```agda
module _
  {l : Level} (R : Ring l)
  where

  is-central-element-mul-Ring :
    (x y : type-Ring R) → is-central-element-Ring R x →
    is-central-element-Ring R y → is-central-element-Ring R (mul-Ring R x y)
  is-central-element-mul-Ring =
    is-central-element-mul-Semiring (semiring-Ring R)
```
