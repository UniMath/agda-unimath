# Local rings

```agda
module ring-theory.local-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import ring-theory.invertible-elements-rings
open import ring-theory.rings
```

</details>

## Idea

A local ring is a ring such that whenever a sum of elements is invertible, then
one of its summands is invertible. This implies that the non-invertible elements
form an ideal. However, the law of excluded middle is needed to show that any
ring of which the non-invertible elements form an ideal is a local ring.

## Definition

```agda
is-local-ring-Prop : {l : Level} (R : Ring l) → Prop l
is-local-ring-Prop R =
  Π-Prop
    ( type-Ring R)
    ( λ a →
      Π-Prop
        ( type-Ring R)
        ( λ b →
          function-Prop
            ( is-invertible-element-Ring R (add-Ring R a b))
            ( disj-Prop
              ( is-invertible-element-ring-Prop R a)
              ( is-invertible-element-ring-Prop R b))))

is-local-Ring : {l : Level} → Ring l → UU l
is-local-Ring R = type-Prop (is-local-ring-Prop R)

is-prop-is-local-Ring : {l : Level} (R : Ring l) → is-prop (is-local-Ring R)
is-prop-is-local-Ring R = is-prop-type-Prop (is-local-ring-Prop R)

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
