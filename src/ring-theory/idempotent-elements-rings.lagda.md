# Idempotent elements in rings

```agda
module ring-theory.idempotent-elements-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import ring-theory.rings
```

</details>

## Idea

An
{{#concept "idempotent element" Disambiguation="in a ring" WD="idempotent element" WDID=Q2243424 Agda=is-idempotent-element-Ring Agda=idempotent-element-Ring}}
in a [ring](ring-theory.rings.md) is an element `x` such that `x² = x`.

## Definition

```agda
module _
  {l : Level} (R : Ring l) (x : type-Ring R)
  where

  is-idempotent-element-ring-Prop : Prop l
  is-idempotent-element-ring-Prop = Id-Prop (set-Ring R) (mul-Ring R x x) x

  is-idempotent-element-Ring : UU l
  is-idempotent-element-Ring = type-Prop is-idempotent-element-ring-Prop

  is-prop-is-idempotent-element-Ring : is-prop is-idempotent-element-Ring
  is-prop-is-idempotent-element-Ring =
    is-prop-type-Prop is-idempotent-element-ring-Prop

idempotent-element-Ring :
  {l : Level} (R : Ring l) → UU l
idempotent-element-Ring R = type-subtype (is-idempotent-element-ring-Prop R)

module _
  {l : Level} (R : Ring l) (x : idempotent-element-Ring R)
  where

  element-idempotent-element-Ring : type-Ring R
  element-idempotent-element-Ring =
    inclusion-subtype (is-idempotent-element-ring-Prop R) x

  is-idempotent-element-idempotent-element-Ring :
    is-idempotent-element-Ring R element-idempotent-element-Ring
  is-idempotent-element-idempotent-element-Ring =
    is-in-subtype-inclusion-subtype (is-idempotent-element-ring-Prop R) x
```
