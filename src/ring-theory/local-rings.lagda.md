# Local rings

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module ring-theory.local-rings
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions funext
open import foundation.disjunction funext univalence truncations
open import foundation.propositions funext univalence
open import foundation.sets funext univalence
open import foundation.universe-levels

open import ring-theory.invertible-elements-rings funext univalence truncations
open import ring-theory.rings funext univalence truncations
```

</details>

## Idea

A local ring is a ring such that whenever a sum of elements is invertible, then
one of its summands is invertible. This implies that the noninvertible elements
form an ideal. However, the law of excluded middle is needed to show that any
ring of which the noninvertible elements form an ideal is a local ring.

## Definition

```agda
is-local-prop-Ring : {l : Level} (R : Ring l) → Prop l
is-local-prop-Ring R =
  Π-Prop
    ( type-Ring R)
    ( λ a →
      Π-Prop
        ( type-Ring R)
        ( λ b →
          function-Prop
            ( is-invertible-element-Ring R (add-Ring R a b))
            ( disjunction-Prop
              ( is-invertible-element-prop-Ring R a)
              ( is-invertible-element-prop-Ring R b))))

is-local-Ring : {l : Level} → Ring l → UU l
is-local-Ring R = type-Prop (is-local-prop-Ring R)

is-prop-is-local-Ring : {l : Level} (R : Ring l) → is-prop (is-local-Ring R)
is-prop-is-local-Ring R = is-prop-type-Prop (is-local-prop-Ring R)

Local-Ring : (l : Level) → UU (lsuc l)
Local-Ring l = Σ (Ring l) is-local-Ring

module _
  {l : Level} (R : Local-Ring l)
  where

  ring-Local-Ring : Ring l
  ring-Local-Ring = pr1 R

  set-Local-Ring : Set l
  set-Local-Ring = set-Ring ring-Local-Ring

  type-Local-Ring : UU l
  type-Local-Ring = type-Ring ring-Local-Ring

  is-local-ring-Local-Ring : is-local-Ring ring-Local-Ring
  is-local-ring-Local-Ring = pr2 R
```
