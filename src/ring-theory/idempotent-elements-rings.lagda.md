# Idempotent elements in rings

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module ring-theory.idempotent-elements-rings
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-products-propositions funext
open import foundation.propositions funext univalence
open import foundation.sets funext univalence
open import foundation.subtypes funext univalence truncations
open import foundation.universe-levels

open import ring-theory.rings funext univalence truncations
```

</details>

## Idea

An idempotent element in a ring is an element `x` such that `x² = x`.

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
