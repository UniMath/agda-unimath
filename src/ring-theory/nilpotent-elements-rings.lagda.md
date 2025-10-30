# Nilpotent elements in rings

```agda
module ring-theory.nilpotent-elements-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.universe-levels

open import ring-theory.nilpotent-elements-semirings
open import ring-theory.powers-of-elements-rings
open import ring-theory.rings
open import ring-theory.subsets-rings
```

</details>

## Idea

A
{{#concept "nilpotent element" Disambiguation="in a ring" Agda=is-nilpotent-element-Ring}}
in a [ring](ring-theory.rings.md) is an element `x` for which there is a
[natural number](elementary-number-theory.natural-numbers.md) `n` such that
`xⁿ = 0`.

## Definition

```agda
module _
  {l : Level} (R : Ring l)
  where

  is-nilpotent-element-ring-Prop : type-Ring R → Prop l
  is-nilpotent-element-ring-Prop =
    is-nilpotent-element-semiring-Prop (semiring-Ring R)

  is-nilpotent-element-Ring : type-Ring R → UU l
  is-nilpotent-element-Ring = is-nilpotent-element-Semiring (semiring-Ring R)

  is-prop-is-nilpotent-element-Ring :
    (x : type-Ring R) → is-prop (is-nilpotent-element-Ring x)
  is-prop-is-nilpotent-element-Ring =
    is-prop-is-nilpotent-element-Semiring (semiring-Ring R)
```

## Properties

### Zero is nilpotent

```agda
is-nilpotent-zero-Ring :
  {l : Level} (R : Ring l) → is-nilpotent-element-Ring R (zero-Ring R)
is-nilpotent-zero-Ring R = is-nilpotent-zero-Semiring (semiring-Ring R)
```

### If `x` and `y` commute and are both nilpotent, then `x + y` is nilpotent

```agda
is-nilpotent-add-Ring :
  {l : Level} (R : Ring l) →
  (x y : type-Ring R) → (mul-Ring R x y ＝ mul-Ring R y x) →
  is-nilpotent-element-Ring R x → is-nilpotent-element-Ring R y →
  is-nilpotent-element-Ring R (add-Ring R x y)
is-nilpotent-add-Ring R = is-nilpotent-add-Semiring (semiring-Ring R)
```

### If `x` is nilpotent, then so is `-x`

```agda
is-nilpotent-element-neg-Ring :
  {l : Level} (R : Ring l) →
  is-closed-under-negatives-subset-Ring R (is-nilpotent-element-ring-Prop R)
is-nilpotent-element-neg-Ring R {x} H =
  apply-universal-property-trunc-Prop H
    ( is-nilpotent-element-ring-Prop R (neg-Ring R x))
    ( λ (n , p) →
      intro-exists n
        ( ( power-neg-Ring R n x) ∙
          ( ( ap (mul-Ring R (power-Ring R n (neg-one-Ring R))) p) ∙
            ( right-zero-law-mul-Ring R (power-Ring R n (neg-one-Ring R))))))
```

### If `x` is nilpotent and `y` commutes with `x`, then `xy` is also nilpotent

```agda
module _
  {l : Level} (R : Ring l)
  where

  is-nilpotent-element-mul-Ring :
    (x y : type-Ring R) →
    mul-Ring R x y ＝ mul-Ring R y x →
    is-nilpotent-element-Ring R x →
    is-nilpotent-element-Ring R (mul-Ring R x y)
  is-nilpotent-element-mul-Ring =
    is-nilpotent-element-mul-Semiring (semiring-Ring R)

  is-nilpotent-element-mul-Ring' :
    (x y : type-Ring R) →
    mul-Ring R x y ＝ mul-Ring R y x →
    is-nilpotent-element-Ring R x →
    is-nilpotent-element-Ring R (mul-Ring R y x)
  is-nilpotent-element-mul-Ring' =
    is-nilpotent-element-mul-Semiring' (semiring-Ring R)
```
