# Division rings

```agda
module ring-theory.division-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.negated-equality
open import foundation.universe-levels

open import ring-theory.invertible-elements-rings
open import ring-theory.nontrivial-rings
open import ring-theory.rings
```

</details>

## Idea

{{#concept "Division rings" Agda=is-division-Ring}} are
[nontrivial rings](ring-theory.nontrivial-rings.md) in which all nonzero
elements are [invertible](ring-theory.invertible-elements-rings.md).

## Definition

```agda
is-division-Ring :
  { l : Level} → Ring l → UU l
is-division-Ring R =
  (is-nontrivial-Ring R) ×
  ((x : type-Ring R) → zero-Ring R ≠ x → is-invertible-element-Ring R x)
```
