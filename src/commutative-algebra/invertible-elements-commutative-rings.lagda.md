# Invertible elements in commutative rings

```agda
module commutative-algebra.invertible-elements-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import foundation.propositions
open import foundation.universe-levels

open import ring-theory.invertible-elements-rings
```

</details>

## Idea

**Invertible elements** are elements that have a two-sided multiplicative
inverse. Such elements are also called the **units** of the Ring. The set of
units of any ring forms a group.

## Definition

```agda
module _
  {l : Level} (A : Commutative-Ring l)
  where

  has-left-inverse-Commutative-Ring : type-Commutative-Ring A → UU l
  has-left-inverse-Commutative-Ring =
    has-left-inverse-Ring (ring-Commutative-Ring A)

  has-right-inverse-Commutative-Ring : type-Commutative-Ring A → UU l
  has-right-inverse-Commutative-Ring =
    has-right-inverse-Ring (ring-Commutative-Ring A)

  has-two-sided-inverse-Commutative-Ring : type-Commutative-Ring A → UU l
  has-two-sided-inverse-Commutative-Ring =
    has-two-sided-inverse-Ring (ring-Commutative-Ring A)

  is-invertible-element-commutative-ring-Prop :
    type-Commutative-Ring A → Prop l
  is-invertible-element-commutative-ring-Prop =
    is-invertible-element-ring-Prop (ring-Commutative-Ring A)

  is-invertible-element-Commutative-Ring : type-Commutative-Ring A → UU l
  is-invertible-element-Commutative-Ring =
    is-invertible-element-Ring (ring-Commutative-Ring A)

  is-prop-is-invertible-element-Commutative-Ring :
    (x : type-Commutative-Ring A) →
    is-prop (is-invertible-element-Commutative-Ring x)
  is-prop-is-invertible-element-Commutative-Ring =
    is-prop-is-invertible-element-Ring (ring-Commutative-Ring A)
```
